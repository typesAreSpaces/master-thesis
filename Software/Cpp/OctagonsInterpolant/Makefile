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
all: tests/test_octagon_parser

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@  $(FLAGS) $< 
# ------------------------------------------------------------------------------------------
#  Tests

.PHONY: tests/test_octagon_parser
tests/test_octagon_parser: $(OBJS) 
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@
	rm -rf tests/*.o $@

.PHONY: tests/test_octagon_constructor
tests/test_octagon_constructor: $(OBJS) 
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@
	rm -rf tests/*.o $@

.PHONY: tests/test_bound_constructor
tests/test_bound_constructor: $(OBJS) 
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@
	rm -rf tests/*.o $@

.PHONY: tests/current_progress
tests/current_progress: $(OBJS) 
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@
	rm -rf tests/*.o $@

# ------------------------------------------------------------------------------------------
.PHONY: clean
clean:
	rm -rf $(ODIR)/* 

#run: ./octagon_interpolator
	#for files in ./tests/smtlib2/*; do \
		#echo $$files; \
		#./octagon_interpolator $$files x2; \
	#done

#old-format: ./octagon_interpolator
	#for files in ./tests/in_format/*; do \
		#./octagon_interpolator $$files; \
	#done

#valgrind-old: ./octagon_interpolator
	#for files in ./tests/in_format/*; do \
		#valgrind ./octagon_interpolator $$files; \
	#done
