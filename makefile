CC=gcc
CFLAGS=-Wno-pointer-sign

build: booyer.c
	$(CC) -g -O0 -o bm booyer.c $(CFLAGS)

clean:
	rm -rf bm
