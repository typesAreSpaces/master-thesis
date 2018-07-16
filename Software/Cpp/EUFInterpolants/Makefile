IDIR = ./include/
ODIR = ./obj/
SDIR = ./src/
CC = g++
CFLAGS = -I$(IDIR) -std=c++11

SRC=$(wildcard $(SDIR)*.cpp)
OBJS=$(patsubst $(SDIR)%.cpp, $(ODIR)%.o, $(SRC))
DEPS=$(wildcard $(IDIR)*.h)

all: main

$(ODIR)%.o: $(SDIR)%.cpp $(DEPS)
	$(CC) -c -o $@ $< -I$(SDIR) $(CFLAGS) 
main: $(OBJS)
	$(CC) -o $@ $^ $(CFLAGS) 
.PHONY: clean
clean:
	rm $(ODIR)*
