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
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS = $(wildcard $(IDIR)/*.h)

TEST_DIR = /home/jose/Downloads/QF_UF/2018-Goel-hwbench
TEST_FILES = $(wildcard $(TEST_DIR)/*.smt2)
TEST_OUTPUT = $(patsubst $(TEST_DIR)/%.smt2, $(TEST_DIR)/%.txt, $(TEST_FILES))

all: euf_interpolator

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@ $(FLAGS) $<

euf_interpolator: $(OBJS) $(Z3DIR)/build/libz3.$(Z3EXT)
	$(CC) -g -o $@ $^ -lpthread

run: euf_interpolator
	./euf_interpolator

valgrind_run: euf_interpolator
	valgrind --log-file="euf_interpolator.txt" ./euf_interpolator

notes:
	grep -nr "// [A-Z][A-Za-z0-9]*: "

.PHONY: clean
clean:
	rm -rf $(ODIR)/* euf_interpolator

test: $(TEST_FILES) euf_interpolator
	for test in $(TEST_FILES); do \
		time ./euf_interpolator $$test; \
	done

