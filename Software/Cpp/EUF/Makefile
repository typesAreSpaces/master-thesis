IDIR = include
ODIR = obj
SDIR = src
CC = g++
CFLAGS = -I$(IDIR) -std=c++11

_DEPS = unionfind.hpp terms.hpp readFile.hpp generateTest.hpp testSolution.hpp formulas.hpp
DEPS = $(patsubst %,$(IDIR)/%,$(_DEPS))

_OBJS = main.o unionfind.o terms.o readFile.o generateTest.o testSolution.o formulas.o
OBJS = $(patsubst %,$(ODIR)/%,$(_OBJS))

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

all: main

main: $(OBJS)
	$(CC) -o $@ $^ $(CFLAGS)

clean:
	rm -f *.o $(OBJS)
