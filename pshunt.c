/* pshunt.c - move MBR partitions around on disk. */
/* Copyright Richard Lupton 2022.                 */
#define _POSIX_C_SOURCE 2
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>
#include <ctype.h>

#include <sys/ioctl.h>
#include <linux/fs.h>

#define LOG(...)    fprintf(stderr, __VA_ARGS__)
#define ERROR(...)  LOG("ERROR: " __VA_ARGS__)
#define UNREACHABLE LOG("PANIC:%s:%u:%s: unreachable codepath hit\n",	\
			__FILE__, __LINE__, __func__), abort()

#define MBR_PARTITION_TABLE_OFFSET           0x1BE
#define MBR_PARTITION_TABLE_RECORD_COUNT     4
#define MBR_BOOT_RECORD_SIGNATURE_OFFSET     0x1FE
#define PARTITION_RECORD_MAX                 ((size_t)512)

#define MAX_SECTOR_SIZE 4096
#define MIN_SECTOR_SIZE 512

/* NOTE trying to reason about what can be stored in off_t is painful.
 * We assert
 *  - it's that same size as size_t
 *  - (SIZE_MAX / 2) can address any byte in any sector
 * Given off_t has the same size as size_t, (SIZE_MAX / 2) should be
 * it's maximum positive value, and hence off_t can be safely used to
 * address bytes on our disks.
 */
_Static_assert(sizeof(off_t) == 8, "off_t has 8 bytes");
_Static_assert(sizeof(size_t) == 8, "size_t has 8 bytes");
_Static_assert((SIZE_MAX >> 1) / MAX_SECTOR_SIZE > UINT32_MAX,
	       "sectors are byte addressable");

enum
{
    RC_OK    = 0,
    RC_ERROR = 1,
};

/* NOTE The 32-bit integers in the MBR are encoded in little endian,
 * so we have a wrapper type to ensure we properly decode these
 * correctly. */
typedef struct uint32_le
{
    union {
	uint32_t n;
	uint8_t byte[4];
    };
} uint32_le;

_Static_assert(sizeof(uint32_le) == sizeof(uint32_t) &&
	       _Alignof(uint32_le) == _Alignof(uint32_t),
	       "uint32_le should be sized and aligned the same as uint32_t");

#ifndef BIG_ENDIAN
#define U32_FROM_LE(u) ((u).n)
#define U32_TO_LE(u) ((uint32_le){ .n = (u) })
#else
#define U32_FROM_LE(u) uint32le_to_be(u)
#define U32_TO_LE(u) uint32_to_le(u)

static inline uint32_t
uint32le_to_be(uint32_le n)
{
    union {
	uint32_t n;
	uint8_t byte[4];
    } reversed = {
	.byte = { n.byte[3], n.byte[2], n.byte[1], n.byte[0] }
    };

    return reversed.n;
}

static inline uint32_le
uint32_to_le(uint32_t n)
{
    union {
	uint32_t n;
	uint8_t byte[4];
    } view = { .n = n };

    return (uint32_le){
	.byte[0] = view.byte[3],
	.byte[1] = view.byte[2],
	.byte[2] = view.byte[1],
	.byte[3] = view.byte[0],
    };
}
#endif

struct partition
{
    uint8_t boot;
    uint8_t start_chs[3];
    uint8_t type_descriptor;
    uint8_t end_chs[3];
    uint32_le sector_start;
    uint32_le sector_count;
};

struct disk
{
    struct {
	uint32_t count;
	uint32_t size;
    } sector;

    struct {
	uint32_t count;
	uint8_t eix;

	struct {
	    uint32_t start[PARTITION_RECORD_MAX];
	    uint32_t count[PARTITION_RECORD_MAX];
	    uint32_t relative[PARTITION_RECORD_MAX];
	} sector;

	struct {
	    uint32_t sector[PARTITION_RECORD_MAX];
	    off_t offset[PARTITION_RECORD_MAX];
	} record;

	struct partition raw[PARTITION_RECORD_MAX];
    } partition;
};

/* IO operations with error reporting */
static int
blkdev_sector_size(int fd, int* out)
{
    errno = 0;
    if (ioctl(fd, BLKSSZGET, out) == -1)
    {
	ERROR("ioctl failed: %s\n", strerror(errno));
	return RC_ERROR;
    }

    return RC_OK;
}

static off_t
seek(int fd, off_t offset, int whence)
{
    errno = 0;
    off_t ret = lseek(fd, offset, whence);

    if (ret == (off_t)-1)
    {
	ERROR("lseek failed: %s\n", strerror(errno));
    }

    return ret;
}

static int
read_exact(int fd, void* buf, size_t count)
{
    assert(count < SSIZE_MAX);

    errno = 0;
    ssize_t bytes = read(fd, buf, count);

    if (bytes < 0)
    {
	ERROR("read error: %s\n", strerror(errno));
	return RC_ERROR;
    }
    else if ((size_t)bytes != count)
    {
	ERROR("read failed - only read %zu bytes of %zu\n", (size_t)bytes, count);
	return RC_ERROR;
    }

    return RC_OK;
}

static int
write_exact(int fd, const void* buf, size_t count)
{
    assert(count < SSIZE_MAX);

    errno = 0;
    ssize_t bytes = write(fd, buf, count);

    if (bytes < 0)
    {
	ERROR("write error: %s\n", strerror(errno));
	return RC_ERROR;
    }
    else if ((size_t)bytes != count)
    {
	ERROR("write failed - only wrote %zu bytes of %zu\n", (size_t)bytes, count);
	return RC_ERROR;
    }

    return RC_OK;
}

static int
filesize(int fd, off_t* out)
{
    off_t end = seek(fd, 0, SEEK_END);

    if (end == (off_t)-1)
    {
	return RC_ERROR;
    }

    if (seek(fd, 0, SEEK_SET) == (off_t)-1)
    {
	return RC_ERROR;
    }

    *out = end;
    return RC_OK;
}

static int
write_record(int fd, off_t offset, struct partition record)
{
    if (seek(fd, offset, SEEK_SET) == ((off_t)-1))
    {
	return RC_ERROR;
    }

    if (write_exact(fd, &record, sizeof(record)))
    {
	return RC_ERROR;
    }

    return RC_OK;
}

/* Retrieve information about partitions */
static inline int
is_extended_partition(uint8_t descriptor)
{
    return descriptor == 0x05 || descriptor == 0x0F;
}

static int
locate_initial_extension(struct partition record[MBR_PARTITION_TABLE_RECORD_COUNT], uint8_t* out)
{
    uint8_t ext = MBR_PARTITION_TABLE_RECORD_COUNT;

    for (uint32_t ix = 0; ix < MBR_PARTITION_TABLE_RECORD_COUNT; ++ix)
    {
	if (is_extended_partition(record[ix].type_descriptor))
	{
	    if (ext != MBR_PARTITION_TABLE_RECORD_COUNT)
	    {
		ERROR("duplicate extended partitions: %d and %d\n", ext, ix);
		return RC_ERROR;
	    }

	    ext = ix;
	}
    }

    *out = ext;
    return RC_OK;
}

static int
is_extension_record(const struct disk* disk, uint32_t ix)
{
    return disk->partition.eix < MBR_PARTITION_TABLE_RECORD_COUNT &&
	ix == disk->partition.eix;
}

/* Core procedure which moves sectors around on disk. Does no
 * checking, just performs the sector moves. */
static int
shunt_sectors(int fd, int sector_size, uint32_t start, uint32_t count, int32_t shunt)
{
    static uint8_t buffer[MAX_SECTOR_SIZE] = { 0 };

    assert(sector_size > 0 && !((size_t)sector_size > sizeof(buffer)));
    const uint32_t init = start + (shunt > 0 ? count - 1 : 0);

    for (uint32_t ix = 0; ix < count; ++ix)
    {
	uint32_t iter = shunt > 0 ? init - ix : init + ix;
	off_t source = iter * sector_size;

	if (seek(fd, source, SEEK_SET) == ((off_t)-1))
	{
	    return RC_ERROR;
	}

	if (read_exact(fd, buffer, sector_size))
	{
	    return RC_ERROR;
	}

	off_t dest = source + (shunt * sector_size);

	if (seek(fd, dest, SEEK_SET) == ((off_t)-1))
	{
	    return RC_ERROR;
	}

	if (write_exact(fd, buffer, sector_size))
	{
	    return RC_ERROR;
	}
    }

    return RC_OK;
}

/* Read layout information from the disk. */
static int
read_partition_table(int fd, off_t offset, struct partition record[MBR_PARTITION_TABLE_RECORD_COUNT])
{
    if (seek(fd, offset, SEEK_SET) == ((off_t)-1))
    {
	return RC_ERROR;
    }

    if (read_exact(fd, record, sizeof(struct partition[MBR_PARTITION_TABLE_RECORD_COUNT])))
    {
	return RC_ERROR;
    }

    return RC_OK;
}

static int
check_boot_signature(int fd)
{
    uint8_t signature[2] = { 0 };

    if (seek(fd, MBR_BOOT_RECORD_SIGNATURE_OFFSET, SEEK_SET) == (off_t)-1)
    {
	return RC_ERROR;
    }

    if (read_exact(fd, signature, sizeof(signature)))
    {
	return RC_ERROR;
    }

    if (signature[0] != 0x55 || signature[1] != 0xAA)
    {
	return RC_ERROR;
    }

    return RC_OK;
}

static int
check_partition_overflow(uint32_t base, uint32_t start, uint32_t count)
{
    if (base + start < base || base + start + count < base + start)
    {
	return RC_ERROR;
    }
    else
    {
	return RC_OK;
    }
}

static int
read_primary_partitions(int fd, struct disk* disk)
{
    if (check_boot_signature(fd))
    {
	ERROR("invalid signature for MBR\n");
	return RC_ERROR;
    }

    if (read_partition_table(fd, MBR_PARTITION_TABLE_OFFSET, disk->partition.raw))
    {
	return RC_ERROR;
    }

    disk->partition.count = MBR_PARTITION_TABLE_RECORD_COUNT;

    disk->partition.record.offset[0] = MBR_PARTITION_TABLE_OFFSET;
    disk->partition.record.offset[1] = MBR_PARTITION_TABLE_OFFSET + sizeof(struct partition);
    disk->partition.record.offset[2] = MBR_PARTITION_TABLE_OFFSET + 2 * sizeof(struct partition);
    disk->partition.record.offset[3] = MBR_PARTITION_TABLE_OFFSET + 3 * sizeof(struct partition);

    disk->partition.sector.start[0] = U32_FROM_LE(disk->partition.raw[0].sector_start);
    disk->partition.sector.start[1] = U32_FROM_LE(disk->partition.raw[1].sector_start);
    disk->partition.sector.start[2] = U32_FROM_LE(disk->partition.raw[2].sector_start);
    disk->partition.sector.start[3] = U32_FROM_LE(disk->partition.raw[3].sector_start);

    disk->partition.sector.count[0] = U32_FROM_LE(disk->partition.raw[0].sector_count);
    disk->partition.sector.count[1] = U32_FROM_LE(disk->partition.raw[1].sector_count);
    disk->partition.sector.count[2] = U32_FROM_LE(disk->partition.raw[2].sector_count);
    disk->partition.sector.count[3] = U32_FROM_LE(disk->partition.raw[3].sector_count);

    disk->partition.sector.relative[0] = disk->partition.sector.start[0];
    disk->partition.sector.relative[1] = disk->partition.sector.start[1];
    disk->partition.sector.relative[2] = disk->partition.sector.start[2];
    disk->partition.sector.relative[3] = disk->partition.sector.start[3];

    for (uint32_t ix = 0; ix < MBR_PARTITION_TABLE_RECORD_COUNT; ++ix)
    {
	const uint32_t start = disk->partition.sector.start[ix];
	const uint32_t count = disk->partition.sector.count[ix];

	if (check_partition_overflow(0, start, count))
	{
	    ERROR("cannot address all sectors in partition %u\n", ix);
	    return RC_ERROR;
	}
	else if (start + count > disk->sector.count)
	{
	    ERROR("partition %u exceeds bounds of disk\n", ix);
	    return RC_ERROR;
	}
    }

    return RC_OK;
}

static int
read_extended_partitions(int fd, struct disk* disk)
{
    int rc = RC_OK;

    if (locate_initial_extension(disk->partition.raw, &disk->partition.eix))
    {
	rc = RC_ERROR;
	goto done;
    }

    if (disk->partition.eix == MBR_PARTITION_TABLE_RECORD_COUNT)
    {
	goto done;
    }

    /* Offsets to the next EBR entry are based off the extended
       partition, while offsets to logical partitions are relative to the
       sector with the EBR describing it. */
    struct partition link = disk->partition.raw[disk->partition.eix];

    const struct {
	uint32_t base;
	uint32_t count;
    } extension = {
	.base = U32_FROM_LE(link.sector_start),
	.count = U32_FROM_LE(link.sector_count),
    };

    assert(!check_partition_overflow(0, extension.base, extension.count));

    uint32_t base = extension.base;
    while (link.type_descriptor)
    {
	/* Check it's safe to read a sector from base */
	if (!(base < extension.count))
	{
	    ERROR("base sector is at end of extended partition - cannot read sector\n");
	    rc = RC_ERROR;
	    goto done;
	}

	/* NOTE base < extension.count <= UINT32_MAX, so adding
	   MBR_PARTITION_TABLE_OFFSET to a sector byte offset can't cause
	   overflow */
	const off_t record_offset = (off_t)base * disk->sector.size + MBR_PARTITION_TABLE_OFFSET;
	struct partition record[MBR_PARTITION_TABLE_RECORD_COUNT] = { 0 };
	static const struct partition zeros[2] = { 0 };

	assert(record_offset > 0);
	if (read_partition_table(fd, record_offset, record))
	{
	    rc = RC_ERROR;
	    goto done;
	}

	if (memcmp(&record[2], zeros, sizeof(zeros)))
	{
	    ERROR("unused extended partition records not zerod\n");
	    rc = RC_ERROR;
	    goto done;
	}

	if (!record[0].type_descriptor)
	{
	    goto done;
	}

	if (!(disk->partition.count < PARTITION_RECORD_MAX))
	{
	    ERROR("exceeded maximum supported partitions %zu\n", PARTITION_RECORD_MAX);
	    rc = RC_ERROR;
	    goto done;
	}

	const uint32_t start = U32_FROM_LE(record[0].sector_start);
	const uint32_t count = U32_FROM_LE(record[0].sector_count);

	/* Check this partition is addressable. */
	if (check_partition_overflow(base, start, count))
	{
	    ERROR("cannot address all sectors in logical partition %u\n", disk->partition.count);
	    rc = RC_ERROR;
	    goto done;
	}

	/* Check this partition is within the extended partition (and hence on the disk). */
	assert(!(extension.count > disk->sector.count));

	if (base + start + count > extension.count)
	{
	    ERROR("logical partition exceeds bounds of extended partition\n");
	    rc = RC_ERROR;
	    goto done;
	}

	disk->partition.raw[disk->partition.count] = record[0];

	disk->partition.sector.start[disk->partition.count] = base + start;
	disk->partition.sector.count[disk->partition.count] = count;
	disk->partition.sector.relative[disk->partition.count] = start;

	disk->partition.record.sector[disk->partition.count] = base;
	disk->partition.record.offset[disk->partition.count] = record_offset;

	disk->partition.count++;

	/* Check jumping to the next record doesn't cause an
	 * overflow, and also addresses within the extended partition. */
	link = record[1];
	const uint32_t link_start = U32_FROM_LE(link.sector_start);
	const uint32_t link_count = U32_FROM_LE(link.sector_count);

	if (check_partition_overflow(extension.base, link_start, link_count))
	{
	    ERROR("linking to logical partition causes exceeds maximum supported sectors\n");
	    rc = RC_ERROR;
	    goto done;
	}
	else if (link_start + link_count > extension.count)
	{
	    ERROR("link record lies outside of extended partition\n");
	    rc = RC_ERROR;
	    goto done;
	}

	base = extension.base + link_start;
    }

done:
    return rc;
}

static int
read_disk_sector_parameters(int fd, uint32_t* size, uint32_t* count)
{
    int rc = RC_OK;

    off_t size_bytes = 0;

    if (filesize(fd, &size_bytes))
    {
	ERROR("failed to get size of file\n");
	rc = RC_ERROR;
	goto end;
    }

    uint32_t sector_size = 0;
    {
	int s = 0;
	if (blkdev_sector_size(fd, &s))
	{
	    ERROR("could not read block size for device\n");
	    rc = RC_ERROR;
	    goto end;
	}

	if (s < MIN_SECTOR_SIZE || s > MAX_SECTOR_SIZE)
	{
	    ERROR("can't support sector size of %d\n", s);
	    rc = RC_ERROR;
	    goto end;
	}

	sector_size = (uint32_t)s;
    }

    assert(sector_size != 0);

    size_t sector_count = size_bytes / sector_size;

    if (sector_count > UINT32_MAX)
    {
	ERROR("disk has %zu sectors, but at most %u are supported\n", sector_count, UINT32_MAX);
	rc = RC_ERROR;
	goto end;
    }

    *size = sector_size;
    *count = sector_count;

end:
    return rc;
}

static int
read_disk(int fd, struct disk* disk)
{
    if (read_disk_sector_parameters(fd, &disk->sector.size, &disk->sector.count))
    {
	return RC_ERROR;
    }

    if (read_primary_partitions(fd, disk))
    {
	ERROR("failed to read primary partitions from MBR on disk\n");
	return RC_ERROR;
    }

    if (read_extended_partitions(fd, disk))
    {
	return RC_ERROR;
    }

    return RC_OK;
}

/* CLI interface */
enum cli_parse_result
{
    CLI_OK,
    CLI_HELP,
    CLI_USAGE_ERROR,
    CLI_ERROR,
    CLI_MAX_CLI_RESULT,
};

enum command
{
    COMMAND_PRINT,
    COMMAND_SHUNT,
    COMMAND_MAX_COMMAND,
};

struct cli
{
    enum command command;
    uint32_t partition_number;
    int32_t shunt;
    int check;
    const char* filename;
};

static void
print_usage(const char* binname)
{
    LOG("%s - shunt DOS partitions on a disk\n\n", binname);
    LOG("print disk partitions:\n");
    LOG("\t%s PATH_TO_DISK\n\n", binname);
    LOG("shunt a partition on a disk:\n");
    LOG("\t%s [-c] -s SECTORS -p PARTITION_INDEX PATH_TO_DISK\n\n", binname);
}

static enum cli_parse_result
parse_cli_opts(int argc, char* argv[], struct cli* out)
{
    enum cli_parse_result rc = CLI_OK;
    enum command command = COMMAND_PRINT;
    int32_t partition = -1;
    int32_t shunt = 0;
    int check = 0;
    const char* filename = NULL;

    int opt = 0;

    while ((opt = getopt(argc, argv, "cp:s:h")) != -1)
    {
	switch (opt)
	{
	    case 'c':
	    {
		check = 1;
	    }
	    break;

	    case 'p':
	    {
		partition = atoi(optarg);
	    }
	    break;

	    case 's':
	    {
		command = COMMAND_SHUNT;
		char* end = 0;
		errno = 0;
		shunt = strtol(optarg, &end, 0);

		if (*end)
		{
		    ERROR("%s is not integer\n", optarg);
		    rc = CLI_ERROR;
		    goto end;
		}
		else if (errno == ERANGE || shunt > INT_MAX || shunt < INT_MIN)
		{
		    ERROR("integer value %s has too great a magnitude\n", optarg);
		    rc = CLI_ERROR;
		    goto end;
		}
	    }
	    break;

	    case 'h':
	    {
		rc = CLI_HELP;
		goto end;
	    }
	    break;

	    default:
	    {
		rc = CLI_USAGE_ERROR;
		goto end;
	    }
	    break;
	}
    }

    if (optind != argc - 1)
    {
	ERROR("single disk path required\n");
	rc = CLI_ERROR;
	goto end;
    }
    else
    {
	filename = argv[optind];
    }

    if (command == COMMAND_SHUNT && partition < 0)
    {
	ERROR("partition number required\n");
	rc = CLI_ERROR;
	goto end;
    }

    assert(rc == CLI_OK);

    *out = (struct cli) {
	.command = command,
	.partition_number = partition,
	.check = check,
	.filename = filename,
	.shunt = shunt,
    };

end:
    return rc;
}

static int
check_request(const struct cli* cli, const struct disk* disk)
{
    int rc = RC_OK;

    /* Check we have a valid partition */
    if (!(cli->partition_number < disk->partition.count) ||
	!disk->partition.raw[cli->partition_number].type_descriptor)
    {
	ERROR("partition %u does not exist\n", cli->partition_number);
	rc = RC_ERROR;
	goto error;
    }

    const uint32_t start = disk->partition.sector.start[cli->partition_number];
    const uint32_t count = disk->partition.sector.count[cli->partition_number];
    const uint32_t record_offset = disk->partition.sector.relative[cli->partition_number];

    /* Check that a negative shunt doesn't move the partition before
       (or over the top of) its boot record. Note that the partition
       record's sector_start entry is relative to the boot record
       describing it. */
    if (cli->shunt < 0 && record_offset - (-cli->shunt + 1) > record_offset)
    {
	ERROR("shunt of %d sectors would move partition before or over its boot record\n", cli->shunt);
	rc = RC_ERROR;
	goto error;
    }

    if (cli->shunt > 0 && start + count + cli->shunt < start + count)
    {
	ERROR("shunt of %d sectors would overflow sector counter\n", cli->shunt);
	rc = RC_ERROR;
	goto error;
    }

    if (cli->shunt > 0 && start + count + cli->shunt > disk->sector.count)
    {
	ERROR("shunt of %d would extend beyond the end of the disk\n", cli->shunt);
	rc = RC_ERROR;
	goto error;
    }

    /* Check that logical partitions stay within the bounds of the
       extended partition. */
    if (cli->partition_number >= MBR_PARTITION_TABLE_RECORD_COUNT)
    {
	assert(disk->partition.eix != MBR_PARTITION_TABLE_RECORD_COUNT);

	const uint32_t extension_start = disk->partition.sector.start[disk->partition.eix];
	const uint32_t extension_count = disk->partition.sector.count[disk->partition.eix];

	if (start + count + (uint32_t)cli->shunt > extension_start + extension_count)
	{
	    ERROR("shunt moves logical partition outside of extended partition %u\n", disk->partition.eix);
	    rc = RC_ERROR;
	    goto error;
	}
    }

    const uint32_t new_start = start + (uint32_t)cli->shunt;
    const uint32_t new_end = new_start + count;

    /* If we're moving the extension container, we only need to check
       entries in the MBR. Everything in the extension container is
       preserved under sector translation. */
    const uint32_t MAXCHECK = is_extension_record(disk, cli->partition_number) ?
	MBR_PARTITION_TABLE_RECORD_COUNT : disk->partition.count;

    for (uint32_t ix = 0; ix < MAXCHECK; ++ix)
    {
	if (ix == cli->partition_number)
	{
	    continue;
	}

	/* Logical partitions must overlap the extended partition, so
	   skip the overlap checks in this case. */
	if (cli->partition_number >= MBR_PARTITION_TABLE_RECORD_COUNT && ix == disk->partition.eix)
	{
	    continue;
	}

	const uint32_t p_start = disk->partition.sector.start[ix];
	const uint32_t p_end = p_start + disk->partition.sector.count[ix];

	/* either the new position is strictly before, or strictly after p */
	if (new_start < p_end && new_end > p_start)
	{
	    ERROR("new position overlaps with partition %u\n", ix);
	    rc = RC_ERROR;
	    goto error;
	}
    }

    /* Check we don't overwrite any boot records. */
    for (uint32_t ix = 0; ix < MAXCHECK; ++ix)
    {
	const uint32_t record_sector = disk->partition.record.sector[ix];

	if (new_start < record_sector + 1 && new_end > record_sector)
	{
	    ERROR("new position overlaps boot record for partition %u\n", ix);
	    rc = RC_ERROR;
	    goto error;
	}
    }

error:
    return rc;
}

int
main(int argc, char* argv[])
{
    int rc = EXIT_SUCCESS;
    int fd = 0;

    struct cli cli = { 0 };
    static struct disk disk = { 0 };

    switch (parse_cli_opts(argc, argv, &cli))
    {
	case CLI_HELP:
	{
	    print_usage(argv[0]);
	    goto end;
	}
	break;

	case CLI_USAGE_ERROR:
	{
	    rc = EXIT_FAILURE;
	    print_usage(argv[0]);
	    goto end;
	}
	break;

	case CLI_ERROR:
	{
	    rc = EXIT_FAILURE;
	    goto end;
	}
	break;

	case CLI_OK:
	{
	    /* Do nothing */
	}
	break;

	case CLI_MAX_CLI_RESULT:
	{
	    UNREACHABLE;
	}
	break;
    }

    static const mode_t command_file_flags[] = {
	[COMMAND_PRINT] = O_RDONLY,
	[COMMAND_SHUNT] = O_RDWR,
    };

    fd = open(cli.filename, command_file_flags[cli.command]);

    if (fd < 0)
    {
	ERROR("failed to open %s: %s\n", cli.filename, strerror(errno));
	rc = EXIT_FAILURE;
	goto end;
    }

    if (read_disk(fd, &disk))
    {
	rc = EXIT_FAILURE;
	goto end;
    }

    switch (cli.command)
    {
	case COMMAND_PRINT:
	{
	    printf("sector size:\t%d\n", disk.sector.size);
	    printf("sector count:\t%u\n", disk.sector.count);

	    for (uint32_t ix = 0; ix < disk.partition.count; ++ix)
	    {
		printf("%d\t0x%.2x\t%s\t%d\t%d\t%c\n", ix, disk.partition.raw[ix].type_descriptor,
		       disk.partition.raw[ix].boot ? "y" : "n", disk.partition.sector.start[ix],
		       disk.partition.sector.count[ix], ix < MBR_PARTITION_TABLE_RECORD_COUNT ? 'P' : 'L');
	    }
	}
	break;

	case COMMAND_SHUNT:
	{
	    if (check_request(&cli, &disk))
	    {
		rc = EXIT_FAILURE;
		goto end;
	    }

	    if (cli.check)
	    {
		LOG("ok\n");
		goto end;
	    }

	    const uint32_t start = disk.partition.sector.start[cli.partition_number];
	    const uint32_t count = disk.partition.sector.count[cli.partition_number];

	    if (shunt_sectors(fd, disk.sector.size, start, count, cli.shunt))
	    {
		ERROR("transferring sectors failed\n");
		rc = EXIT_FAILURE;
		goto end;
	    }

	    /* Update and write back record. */
	    struct partition r = disk.partition.raw[cli.partition_number];
	    r.sector_start = U32_TO_LE(U32_FROM_LE(r.sector_start) + cli.shunt);

	    if (write_record(fd, disk.partition.record.offset[cli.partition_number], r))
	    {
		ERROR("failed to write updated record to %s\n", cli.filename);
		rc = EXIT_FAILURE;
		goto end;
	    }
	}
	break;

	case COMMAND_MAX_COMMAND:
	{
	    UNREACHABLE;
	}
	break;
    }

end:
    if (fd > 0)
    {
	close(fd);
    }

    return rc;
}
