Z3DIR = /Users/joseabelcastellanosjoo/Documents/Applications/z3
IDIR = ./include
ODIR = ./obj
SDIR = ./src
CC = g++
FLAGS = -I$(SDIR)/ -I$(IDIR)/ -std=c++11

SRC = $(wildcard $(SDIR)/*.cpp)
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS = $(wildcard $(IDIR)/*.h)

all: main

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -c -o$@  $(FLAGS) $< -Wall
main: $(OBJS) $(Z3DIR)/build/libz3.dylib
	$(CC) -o$@ $^ -lpthread -Wall
test_old:
	for x in ./tests/old/*; do echo $$x; ./main $$x; done
test_smt2:
	for x in ./tests/smt2lib/*; do echo $$x; ./main $$x; done
.PHONY: clean
clean:
	rm -rf $(ODIR)/* main
