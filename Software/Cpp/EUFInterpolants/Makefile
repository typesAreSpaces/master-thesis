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
FLAGS = -I$(SDIR)/ -I$(IDIR)/ -std=c++11

SRC = $(wildcard $(SDIR)/*.cpp)
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS = $(wildcard $(IDIR)/*.h)

CONGRUENCE_CLOSURE_TEST = performance/congruence_closure

all: main

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@  $(FLAGS) $< -Wall

main: $(OBJS) $(Z3DIR)/build/libz3.$(Z3EXT)
	$(CC) -g -o $@ $^ -lpthread -Wall

check_correctness_congruence_closure:
	$(CC) -o $(CONGRUENCE_CLOSURE_TEST)/$@ $(CONGRUENCE_CLOSURE_TEST)/congruence_closure_performance.cpp -I./include -I./src -std=c++11 obj/CircularList.o obj/CongruenceClosure.o obj/Signature.o obj/SignatureTable.o obj/Terms.o obj/UnionFind.o obj/Term.o $(Z3DIR)/build/libz3.$(Z3EXT)
	rm -rf $(CONGRUENCE_CLOSURE_TEST)/$@.txt
	touch $(CONGRUENCE_CLOSURE_TEST)/$@.txt
	for directories in /Users/joseabelcastellanosjoo/master-thesis/Software/Cpp/EUFInterpolants/tests/congruence_closure/*; do \
		for files in $$directories; do \
			./$(CONGRUENCE_CLOSURE_TEST)/$@ $$files;  \
		done; \
	done

check_performance_congruence_closure:
	$(CC) -o $(CONGRUENCE_CLOSURE_TEST)/$@ $(CONGRUENCE_CLOSURE_TEST)/congruence_closure_performance.cpp -I./include -I./src -std=c++11 obj/CircularList.o obj/CongruenceClosure.o obj/Signature.o obj/SignatureTable.o obj/Terms.o obj/UnionFind.o obj/Term.o $(Z3DIR)/build/libz3.$(Z3EXT)
	rm -rf $(CONGRUENCE_CLOSURE_TEST)/$@.txt
	touch $(CONGRUENCE_CLOSURE_TEST)/$@.txt
	for directories in /Users/joseabelcastellanosjoo/Desktop/congruence_closure_performance_samples/*; do \
		for files in $$directories/*; do \
			./$(CONGRUENCE_CLOSURE_TEST)/$@ $$files >> $(CONGRUENCE_CLOSURE_TEST)/$@.txt;  \
		done; \
	done
	$(CC) -o $(CONGRUENCE_CLOSURE_TEST)/processing $(CONGRUENCE_CLOSURE_TEST)/processing.cpp
	rm -rf $(CONGRUENCE_CLOSURE_TEST)/results.txt
	touch $(CONGRUENCE_CLOSURE_TEST)/results.txt
	./$(CONGRUENCE_CLOSURE_TEST)/processing $(CONGRUENCE_CLOSURE_TEST)/$@.txt > $(CONGRUENCE_CLOSURE_TEST)/results.txt

run : main
#	./main ./tests/smt2lib_2/kapurEUFExample.smt2 v
#	./main ./tests/smt2lib_2/simple.smt2 f 
#	./main ./tests/smt2lib_2/simple2.smt2 f
	./main ./tests/smt2lib_2/simple2_2.smt2 f
#	./main ./tests/smt2lib_2/simple3.smt2 f
#	./main ./tests/smt2lib_2/three_arguments.smt2 f
#	./main ./tests/smt2lib_2/three_arguments2.smt2 f
#	./main ./tests/smt2lib_2/three_arguments3.smt2 f
#	./main ./tests/smt2lib_2/kapurEUFExample2.smt2 f
#	./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 f
#	./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 y$1
#	./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2 f
#	./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2 f

debug : main
	gdb --args ./main ./tests/smt2lib_2/kapurEUFExample.smt2 v
#	gdb --args ./main ./tests/smt2lib_2/simple.smt2 f 
#	gdb --args ./main ./tests/smt2lib_2/simple2.smt2 f
#	gdb --args ./main ./tests/smt2lib_2/simple3.smt2 f
#	gcd --args ./main ./tests/smt2lib_2/three_arguments.smt2 f
#	gcd --args ./main ./tests/smt2lib_2/three_arguments2.smt2 f
#	gcd --args ./main ./tests/smt2lib_2/three_arguments3.smt2 f		
#	gdb --args ./main ./tests/smt2lib_2/kapurEUFExample2.smt2 f
#	gdb --args ./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 f
#	gdb --args ./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 y$1
#	gdb --args ./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2 f
#	gdb --args ./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2 f

valgrind : main
	valgrind ./main ./tests/smt2lib_2/kapurEUFExample.smt2 v
#	valgrind ./main ./tests/smt2lib_2/simple.smt2 f 
#	valgrind ./main ./tests/smt2lib_2/simple2.smt2 f
#	valgrind ./main ./tests/smt2lib_2/simple2.smt3 f
#	valgrind ./main ./tests/smt2lib_2/three_arguments.smt2 f
#	valgrind ./main ./tests/smt2lib_2/three_arguments2.smt2 f
#	valgrind ./main ./tests/smt2lib_2/three_arguments3.smt2 f
#	valgrind ./main ./tests/smt2lib_2/kapurEUFExample2.smt2 f
#	valgrind ./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 f
#	valgrind ./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 y$1
#	valgrind ./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2 f
#	valgrind ./main /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2 f

.PHONY: clean
clean:
	rm -rf $(ODIR)/* main
