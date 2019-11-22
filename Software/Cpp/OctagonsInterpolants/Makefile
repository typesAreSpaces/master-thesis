UNAME = $(shell uname)
WHO = $(shell whoami)
ifeq ($(UNAME), Linux)
	ifeq ($(WHO), jose.castellanosjoo)
	Z3DIR = /nfs/student/j/jose.castellanosjoo/Documents/GitProjects/z3
	endif
	ifeq ($(WHO), jose)
# Z3DIR = /home/jose/Documents/Github\ Projects/z3
	Z3DIR = /home/jose/Documents/GithubProjects/z3
	endif
Z3EXT = so
endif
ifeq ($(UNAME), Darwin)
Z3DIR = /Users/joseabelcastellanosjoo/Documents/Applications/z3
Z3EXT = dylib
endif

IDIR = ./include
ODIR = ./obj
SDIR = ./src
CC = g++
FLAGS = -I$(IDIR)/ -std=c++11

SRC = $(wildcard $(SDIR)/*.cpp)
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS = $(wildcard $(IDIR)/*.h)

all: main


$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@  $(FLAGS) $< -Wall

main: $(OBJS) $(Z3DIR)/build/libz3.$(Z3EXT)
	$(CC) -g -o $@ $^ -lpthread -Wall

clean:
	rm -f $(OBJS)

problem: ./main
	./main ./tests/smtlib2/test7.smt2 x2

runsmt2: ./main
	for files in /home/jose/Documents/GithubProjects/master-thesis/Software/Cpp/OctagonsInterpolants/tests/smtlib2/*; do \
		./main $$files x2; \
	done

old-format: ./main
	for files in /home/jose/Documents/GithubProjects/master-thesis/Software/Cpp/OctagonsInterpolants/tests/in_format/*; do \
		./main $$files; \
	done

valgrind-old: ./main
	for files in /home/jose/Documents/GithubProjects/master-thesis/Software/Cpp/OctagonsInterpolants/tests/in_format/*; do \
		valgrind ./main $$files; \
	done
