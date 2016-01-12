
CC := clang-3.5
CCFLAGS := -Wall
OPT := opt
OPTFLAGS := -O3
LLC := llc

main: main.o libnarith_ops.so
	$(CC) $(CCFLAGS) -o main main.o -L. -l narith_ops

main.o : main.c ops.h
	$(CC) $(CCFLAGS) -c main.c

main.s : main.c ops.h
	$(CC) $(CCFLAGS) -S main.c

ops.s : ops.ll
	$(OPT) $(OPTFLAGS) ops.ll | $(LLC) -o=ops.s

libnarith_ops.so : ops.o
	$(CC) -shared ops.o -o libnarith_ops.so

.PHONY: run
run:
	@LD_LIBRARY_PATH=.:$(LD_LIBRARY_PATH) ./main

clean:
	rm -f main
	rm -f libnarith_ops.so
	rm -f *.o *.s
	../../../build/clean.pl
