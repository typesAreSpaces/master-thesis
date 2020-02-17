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
FLAGS = -I$(SDIR) -I$(IDIR) -std=c++11

SRC = $(wildcard $(SDIR)/*.cpp)
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS = $(wildcard $(IDIR)/*.h)

all: euf_interpolator

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@  $(FLAGS) $< -Wall

euf_interpolator: $(OBJS) $(Z3DIR)/build/libz3.$(Z3EXT)
	$(CC) -g -o $@ $^ -lpthread -Wall

.PHONY: clean
clean:
	rm -rf $(ODIR)/* euf_interpolator
