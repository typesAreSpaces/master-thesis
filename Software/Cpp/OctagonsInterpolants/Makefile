IDIR = ./include/
ODIR = ./obj/
SDIR = ./src/
CC = g++
CFLAGS = -I$(IDIR) -std=c++11

DEPS = $(wildcard $(IDIR)*.h)
SRC = $(wildcard $(SDIR)*.cpp)
OBJS = $(patsubst $(SDIR)%.cpp, $(ODIR)%.o, $(SRC))

all: main

$(ODIR)%.o: $(SDIR)%.cpp $(DEPS)
	$(CC) -c -o $@ $< $(CFLAGS)

main: $(OBJS)
	$(CC) -o $@ $^

clean:
	rm -f $(OBJS)
