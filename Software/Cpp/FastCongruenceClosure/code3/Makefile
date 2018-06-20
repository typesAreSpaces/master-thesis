IDIR = include
ODIR = obj
SDIR = src
CC = g++
CFLAGS = -I$(IDIR) -std=c++11

_DEPS = unionfind.hpp node.hpp signatureTable.hpp congruenceClosure.hpp
DEPS = $(patsubst %,$(IDIR)/%,$(_DEPS))

_OBJS = congruenceClosure.o main.o produceRandomEqs.o
OBJS = $(patsubst %,$(ODIR)/%,$(_OBJS))

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

all: main

main: $(OBJS)
	$(CC) -o $@ $^ $(CFLAGS)
