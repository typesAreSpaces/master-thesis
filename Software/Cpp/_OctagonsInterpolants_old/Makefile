IDIR = include
ODIR = obj
SDIR = src
CC = g++
CFLAGS = -I$(IDIR) -std=c++11

_DEPS = structures.hpp readFile.hpp interpolationOct.hpp generateTest.hpp testSolution.hpp 
DEPS = $(patsubst %,$(IDIR)/%,$(_DEPS))

_OBJS = main.o structures.o readFile.o interpolationOct.o generateTest.o testSolution.o
OBJS = $(patsubst %,$(ODIR)/%,$(_OBJS))

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

all: main

main: $(OBJS)
	$(CC) -o $@ $^ $(CFLAGS)

clean:
	rm -f *.o $(OBJS)
