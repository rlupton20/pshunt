# pshunt

Utility for moving partitions controlled by a MBR. Supports moving primary and logical partitions, as well as the entire extended partition.

Not tested on big endian machines (compile with `-DBIG_ENDIAN`).

## Build

```
$ gcc -o pshunt -std=c11 -Wall -Wextra -Werror -pedantic pshunt.c
```

## Usage

List partition information (also gives the index for referring to a partition):

```
$ pshunt DEVICE_PATH
```

Check if a move of a partition is safe:

```
$ pshunt -c -s SECTORS_TO_MOVE -p PARTITON_INDEX DEVICE_PATH
```

Note that `SECTORS_TO_MOVE` can be positive (move right) or negative (move left).

Perform the move;

```
$ pshunt -s SECTORS_TO_MOVE -p PARTITON_INDEX DEVICE_PATH
```

## License

MIT.