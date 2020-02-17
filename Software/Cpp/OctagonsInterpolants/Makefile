UNAME = $(shell uname)
WHO = $(shell whoami)
ifeq ($(UNAME), Linux)
	ifeq ($(WHO), jose.castellanosjoo)
	Z3DIR = /nfs/student/j/jose.castellanosjoo/Documents/GitProjects/z3__
	endif
	ifeq ($(WHO), jose)
# Z3DIR = /home/jose/Documents/Github\ Projects/z3__
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
FLAGS = -I$(IDIR) -std=c++11

SRC = $(wildcard $(SDIR)/*.cpp)
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS = $(wildcard $(IDIR)/*.h)

all: octagon_interpolator

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@  $(FLAGS) $< -Wall

octagon_interpolator: $(OBJS) $(Z3DIR)/build/libz3.$(Z3EXT)
	$(CC) -g -o $@ $^ -lpthread -Wall

run: ./octagon_interpolator
	for files in ./tests/smtlib2/*; do \
		echo $$files; \
		./octagon_interpolator $$files x2; \
	done

old-format: ./octagon_interpolator
	for files in ./tests/in_format/*; do \
		./octagon_interpolator $$files; \
	done

valgrind-old: ./octagon_interpolator
	for files in ./tests/in_format/*; do \
		valgrind ./octagon_interpolator $$files; \
	done

.PHONY: clean
clean:
	rm -rf $(ODIR)/* octagon_interpolator
