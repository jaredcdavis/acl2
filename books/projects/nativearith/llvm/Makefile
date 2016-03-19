
CC := clang
CCFLAGS := -Wall
OPT := opt
OPTFLAGS := -O3
LLC := llc
ASM := as

.PHONY: all
all: main demo

main: main.o libnarith_ops.so
	$(CC) $(CCFLAGS) -o main main.o -L. -l narith_ops

main.o : main.c ops.h
	$(CC) $(CCFLAGS) -c main.c

main.s : main.c ops.h
	$(CC) $(CCFLAGS) -S main.c

ops.s : ops.ll
	$(OPT) $(OPTFLAGS) ops.ll | $(LLC) -o=ops.s

ops.o : ops.s
	$(ASM) ops.s -o ops.o

libnarith_ops.so : ops.o
	$(CC) -shared ops.o -o libnarith_ops.so

demo: demo.c demo.o
	$(CC) $(CCFLAGS) demo.c demo.o -o demo

demo.s : demo.ll
	$(OPT) $(OPTFLAGS) demo.ll -o=demo.ll.opt --time-passes
	$(LLC) -o demo.s demo.ll.opt

demo.o : demo.s
	$(ASM) demo.s -o demo.o
	ls -l demo.o


tmp.o : tmp.c
	$(CC) $(CCFLAGS) -c tmp.c

tmp : tmp.o narith_tmp/libfoo.so
	$(CC) $(CCFLAGS) -o tmp tmp.o -Lnarith_tmp -l foo

.PHONY: runtmp
runtmp:
	@LD_LIBRARY_PATH=./narith_tmp:$(LD_LIBRARY_PATH) ./tmp


.PHONY: run
run:
	@LD_LIBRARY_PATH=.:$(LD_LIBRARY_PATH) ./main

clean:
	rm -f main demo
	rm -f libnarith_ops.so
	rm -f *.o *.s
	../../../build/clean.pl
