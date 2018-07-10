IDIR = ./include/
ODIR = ./obj/
SDIR = ./src/
CC = g++
CFLAGS = -I$(IDIR) -std=c++11

SRC=$(wildcard $(SDIR)*.cpp)
OBJS=$(patsubst %.cpp, %.o, $(SRC))
DEPS=$(wildcard $(IDIR)*.h)

_OBJST= node main LinkedList CircularList vertex GTerms unionfind signatureTable signature
OBJST=$(patsubst %, $(ODIR)%.o, $(_OBJST))

all:
	for x in $(_OBJST); do\
		g++ -c -o $(ODIR)$$x.o $(SDIR)$$x.cpp -I$(SDIR) $(CFLAGS); \
	done 
	g++ -o main $(OBJST) $(CFLAGS)

run:
	./main test/example2.txt

#$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS) \
	$(CC) -c -o $@ $< $(CFLAGS) \
main: $(OBJS) \
#	$(CC) -o $@ $^ $(CFLAGS) 
