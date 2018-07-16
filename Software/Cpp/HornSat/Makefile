IDIR=./include/
SDIR=./src/
ODIR=./obj/
CC=g++
DEPS=$(wildcard $(IDIR)*.h)
SRC=$(wildcard $(SDIR)*.cpp)
OBJS=$(patsubst $(SDIR)%.cpp, $(ODIR)%.o, $(SRC))
CFLAGS= -I$(IDIR)
TESTS=$(wildcard ./examples/*)

all: main

$(ODIR)%.o: $(SDIR)%.cpp $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

main: $(OBJS)
	$(CC) -o $@ $^

.PHONY: clean

clean:
	rm $(ODIR)*.o ./*\~

test:
	for test in $(TESTS); do\
		echo 'Test: '$$test; \
		./main < $$test; \
	done
