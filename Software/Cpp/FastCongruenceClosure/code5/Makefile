IDIR = ./include/
ODIR = ./obj/
SDIR = ./src/
CC = g++
CFLAGS = -I$(IDIR) -std=c++11

SRC=$(wildcard $(SDIR)*.cpp)
OBJS=$(patsubst *.cpp, *.o, $(SRC))
DEPS=$(wildcard $(IDIR)*.h)

all:
	echo 'hello'
	g++ -c -o $(ODIR)node.o $(IDIR)node.h
	g++ -o node $(ODIR)node.o
#all: main \

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS) \
	$(CC) -c -o $@ $< $(CFLAGS)\

main: $(OBJS)\
#	$(CC) -o $@ $^ $(CFLAGS)\
