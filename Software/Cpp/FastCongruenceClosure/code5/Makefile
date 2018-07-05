IDIR = ./include/
ODIR = ./obj/
SDIR = ./src/
CC = g++
CFLAGS = -I$(IDIR) -std=c++11

SRC=$(wildcard $(SDIR)*.cpp)
OBJS=$(patsubst %.cpp, %.o, $(SRC))
DEPS=$(wildcard $(IDIR)*.h)

_OBJST= node main LinkedList CircularList vertex GTerms
OBJST=$(patsubst %, $(ODIR)%.o, $(_OBJST))

all:
	for x in $(_OBJST); do\
		g++ -c -o $(ODIR)$$x.o $(SDIR)$$x.cpp $(CFLAGS); \
	done 
	g++ -o main $(OBJST) $(CFLAGS)

#$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS) \
	$(CC) -c -o $@ $< $(CFLAGS) \
main: $(OBJS) \
#	$(CC) -o $@ $^ $(CFLAGS) 
