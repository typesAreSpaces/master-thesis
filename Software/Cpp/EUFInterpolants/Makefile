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
	$(CC) -c -o $@  $(FLAGS) $< -Wall

main: $(OBJS) $(Z3DIR)/build/libz3.dylib
	$(CC) -o $@ $^ -lpthread -Wall

check_performance_congruence_closure:
	$(CC) -o $@ performance/congruence_closure_performance.cpp -I./include -I./src -std=c++11 obj/CircularList.o obj/CongruenceClosure.o obj/Signature.o obj/SignatureTable.o obj/Terms.o obj/UnionFind.o obj/Vertex.o $(Z3DIR)/build/libz3.dylib
	for directories in /Users/joseabelcastellanosjoo/Desktop/congruence_closure_performance_samples/*; do \
		for files in $$directories/*; do \
			./$@ $$files; \
		done; \
	done

test_old:
	for x in ./tests/old/*; do \
		echo $$x; \
		./main $$x; \
	done
test_smt2:
	for x in ./tests/smt2lib/*; do \
		echo $$x; \
		./main $$x; \
	done

.PHONY: clean
clean:
	rm -rf $(ODIR)/* main
