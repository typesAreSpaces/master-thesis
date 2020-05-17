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

#all: tests/cong_closure_expl_test
all: tests/current_progress
#all: valgrind_run

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@ $(FLAGS) $<

.PHONY: tests/current_progress
tests/current_progress: $(OBJS)
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread
	./$@
	rm -rf tests/*.o $@

.PHONY: valgrind_run
valgrind_run: $(OBJS)
	$(CC) -g -c -o ./tests/current_progress.o $(FLAGS) ./tests/current_progress.cpp
	$(CC) -g -o tests/current_progress $(OBJS) ./tests/current_progress.o -lpthread
	valgrind --log-file="output.txt" ./tests/current_progress
	rm -rf tests/*.o tests/current_progress

.PHONY: tests/cong_closure_expl_test
tests/cong_closure_expl_test: $(OBJS)
	$(CC) -g -c -o tests/TestCongruenceClosureExplain.o $(FLAGS) tests/TestCongruenceClosureExplain.cpp
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) tests/TestCongruenceClosureExplain.o ./$@.o -lpthread
	./$@
	rm -rf tests/*.o $@

.PHONY: tests/qf_uf_processing_test
tests/qf_uf_test: $(OBJS)
	$(CC) -g -c -o tests/TestCongruenceClosureExplain.o $(FLAGS) tests/TestCongruenceClosureExplain.cpp
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) tests/TestCongruenceClosureExplain.o ./$@.o -lpthread
	./$@.sh
	rm -rf tests/*.o $@

notes:
	grep -nr "// [A-Z][A-Za-z0-9]*: "

.PHONY: clean
clean:
	rm -rf $(ODIR)/* 
