IDIR = ./include/
ODIR = ./obj/
SDIR = ./src/
CC = g++
CFLAGS = -I$(IDIR) -std=c++11

SRC=$(wildcard $(SDIR)*.cpp)
OBJS=$(patsubst $(SDIR)%.cpp, $(ODIR)%.o, $(SRC))
DEPS=$(wildcard $(IDIR)*.h)

all: main

$(ODIR)%.o: $(SDIR)%.cpp $(DEPS) $(SRC)
	$(CC) -c -o $@ $< -I$(SDIR) $(CFLAGS) 
main: $(OBJS)
	$(CC) -o $@ $^ $(CFLAGS) 
run:
	./main test/example2.txt
.PHONY: clean
clean:
	rm *\~ $(ODIR)*
