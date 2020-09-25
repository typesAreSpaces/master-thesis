UNAME = $(shell uname)
WHO = $(shell whoami)
ifeq ($(UNAME), Linux)
	ifeq ($(WHO), jose.castellanosjoo)
	Z3DIR = /nfs/student/j/jose.castellanosjoo/Documents/GitProjects/z3__
	endif
	ifeq ($(WHO), jose)
	Z3DIR = /home/jose/Documents/GithubProjects/z3__
	endif
Z3EXT = so
endif
ifeq ($(UNAME), Darwin)
Z3DIR = /Users/joseabelcastellanosjoo/Documents/Applications/z3__
Z3EXT = dylib
endif

IDIR = ./include
ODIR = ./obj
SDIR = ./src
CC = g++
FLAGS = -I$(SDIR) -I$(IDIR) -std=c++11 -Wall

SRC = $(wildcard $(SDIR)/*.cpp)
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC)) $(Z3DIR)/build/libz3.$(Z3EXT) 
DEPS = $(wildcard $(IDIR)/*.h)

# ------------------------------------------------------------------------------------------
#  Build
#all: bin/octi
#all: tests/test_octagon_parser
#all: tests/current_progress
all: tests/parametric_example

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@  $(FLAGS) $< 

# ------------------------------------------------------------------------------------------
#  Binaries

bin/octi: $(OBJS) ./tests/octi.cpp
	$(CC) -g -c -o ./tests/octi.o $(FLAGS) ./tests/octi.cpp
	$(CC) -g -o ./bin/octi $(OBJS) ./tests/octi.o -lpthread -Wall
	rm -rf tests/*.o


# ------------------------------------------------------------------------------------------
#  Tests

.PHONY: tester
tester: $(OBJS)
	$(CC) -g -c -o ./$(param1).o $(FLAGS) ./$(param1).cpp
	$(CC) -g -o $(param1) $(OBJS) ./$(param1).o -lpthread -Wall
	./$(param1)
	rm -rf tests/*.o $(param1)

.PHONY: tests/test_octagon_parser
tests/test_octagon_parser: $(OBJS) 
	make tester param1=tests/test_octagon_parser

.PHONY: tests/test_octagon_constructor
tests/test_octagon_constructor: $(OBJS) 
	make tester param1=tests/test_octagon_constructor

.PHONY: tests/test_bound_constructor
tests/test_bound_constructor: $(OBJS) 
	make tester param1=tests/test_bound_constructor

.PHONY: tests/current_progress
tests/current_progress: $(OBJS) 
	make tester param1=tests/current_progress

.PHONY: tests/parametric_example
tests/parametric_example:
	$(CC) -g -o ./tests/parametric_example ./tests/parametric_example.cpp -pthread
	./tests/parametric_example
	rm -rf ./tests/parametric_example



# ------------------------------------------------------------------------------------------
.PHONY: clean
clean:
	rm -rf $(ODIR)/* 
