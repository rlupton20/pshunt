#!/bin/sh

set -e

OUT=$(readlink -f "$1")

dd if=/dev/zero of="$OUT" bs=1M count=100

fdisk "$OUT" <<EOF
o
n
p
1
2048
+128
a
n
p
2
4096
+128
n
e
3
6144
+131072
n
l
8192
+128
n
l
12288
+256
w
EOF


cleanup() {
    if [ -e "$MOUNT" ]
    then
	echo "Unmounting $MOUNT"
	umount "$MOUNT"
	rmdir "$MOUNT"
    fi

    if [ -e "$LOOPDEV" ]
    then
	echo "Detaching $LOOPDEV"
	losetup --detach "$LOOPDEV"
    fi

}

trap cleanup 0

LOOPDEV=$(losetup -P --show -f "$OUT")
mkfs.ext2 "${LOOPDEV}p1"
mkfs.ext2 "${LOOPDEV}p2"
mkfs.ext2 "${LOOPDEV}p5"
mkfs.ext2 "${LOOPDEV}p6"

MOUNT=$(mktemp -d)
for i in 1 2 5 6
do
    mount "${LOOPDEV}p${i}" "$MOUNT"
    echo "foobarfutz-${i}" > "${MOUNT}/file"
    umount "$MOUNT"
done


