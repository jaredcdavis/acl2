
CC := clang-3.5
CCFLAGS := -Wall
OPT := opt
OPTFLAGS := -O3
LLC := llc

main: main.o ops.o
	$(CC) $(CCFLAGS) -o main $^

main.o : main.c
	$(CC) $(CCFLAGS) -c main.c

main.s : main.c
	$(CC) $(CCFLAGS) -S main.c

ops.s : ops.ll
	$(OPT) $(OPTFLAGS) ops.ll | $(LLC) -o=ops.s

clean:
	rm -f main
	rm -f *.o *.s
