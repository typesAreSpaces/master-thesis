IDIR = ./include/
ODIR = ./obj/
SDIR = ./src/
CC = g++
CFLAGS = -I$(IDIR) -std=c++11

SRC=$(wildcard $(SDIR)*.cpp)
OBJS=$(patsubst %.cpp, %.o, $(SRC))
DEPS=$(wildcard $(IDIR)*.h)
_OBJST= node.o main.o LinkedList.o CircularList.o vertex.o GTerms.o
OBJST=$(patsubst %, $(ODIR)%, $(_OBJST))

all:
	g++ -c -o $(ODIR)node.o $(SDIR)node.cpp $(CFLAGS)
	g++ -c -o $(ODIR)LinkedList.o $(SDIR)LinkedList.cpp $(CFLAGS)
	g++ -c -o $(ODIR)CircularList.o $(SDIR)CircularList.cpp $(CFLAGS)
	g++ -c -o $(ODIR)node.o $(SDIR)node.cpp $(CFLAGS)
	g++ -c -o $(ODIR)vertex.o $(SDIR)vertex.cpp $(CFLAGS)
	g++ -c -o $(ODIR)GTerms.o $(SDIR)GTerms.cpp $(CFLAGS)
	g++ -c -o $(ODIR)main.o $(SDIR)main.cpp $(CFLAGS)
	g++ -o main $(OBJST) $(CFLAGS)

#$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS) \
	$(CC) -c -o $@ $< $(CFLAGS) \

main: $(OBJS) \
#	$(CC) -o $@ $^ $(CFLAGS) 
