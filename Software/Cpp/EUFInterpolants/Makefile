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
FLAGS = -I$(SDIR) -I$(IDIR) -std=c++11

SRC = $(wildcard $(SDIR)/*.cpp)
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS = $(wildcard $(IDIR)/*.h)

CONGRUENCE_CLOSURE_TEST = ./performance/congruence_closure

all: euf_interpolator

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@  $(FLAGS) $< -Wall

euf_interpolator: $(OBJS) $(Z3DIR)/build/libz3.$(Z3EXT)
	$(CC) -g -o $@ $^ -lpthread -Wall

# no longer used
check_correctness_congruence_closure:
	$(CC) -o $(CONGRUENCE_CLOSURE_TEST)/$@ $(CONGRUENCE_CLOSURE_TEST)/congruence_closure_performance.cpp -I./include -I./src -std=c++11 obj/CircularList.o obj/CongruenceClosure.o obj/Signature.o obj/SignatureTable.o obj/Terms.o obj/UnionFind.o obj/Term.o $(Z3DIR)/build/libz3.$(Z3EXT)
	rm -rf $(CONGRUENCE_CLOSURE_TEST)/$@.txt
	touch $(CONGRUENCE_CLOSURE_TEST)/$@.txt
	for directories in ./tests/congruence_closure/*; do \
		for files in $$directories; do \
			./$(CONGRUENCE_CLOSURE_TEST)/$@ $$files;  \
		done; \
	done

# no longer used
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

run : euf_interpolator
#	./euf_interpolator ./tests/smtlib2_files/kapurEUFExample.smt2 v
#	./euf_interpolator ./tests/smtlib2_files/simple.smt2 f 
#	./euf_interpolator ./tests/smtlib2_files/simple2.smt2 f
	./euf_interpolator ./tests/smtlib2_files/simple2_2.smt2 f
#	./euf_interpolator ./tests/smtlib2_files/simple3.smt2 f
#	./euf_interpolator ./tests/smtlib2_files/three_arguments.smt2 f
#	./euf_interpolator ./tests/smtlib2_files/three_arguments2.smt2 f
#	./euf_interpolator ./tests/smtlib2_files/three_arguments3.smt2 f
#	./euf_interpolator ./tests/smtlib2_files/kapurEUFExample2.smt2 f
#	./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 f
#	./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 y$1
#	./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2 f
#	./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2 f

debug : euf_interpolator
	gdb --args ./euf_interpolator ./tests/smtlib2_files/kapurEUFExample.smt2 v
#	gdb --args ./euf_interpolator ./tests/smtlib2_files/simple.smt2 f 
#	gdb --args ./euf_interpolator ./tests/smtlib2_files/simple2.smt2 f
#	gdb --args ./euf_interpolator ./tests/smtlib2_files/simple3.smt2 f
#	gcd --args ./euf_interpolator ./tests/smtlib2_files/three_arguments.smt2 f
#	gcd --args ./euf_interpolator ./tests/smtlib2_files/three_arguments2.smt2 f
#	gcd --args ./euf_interpolator ./tests/smtlib2_files/three_arguments3.smt2 f		
#	gdb --args ./euf_interpolator ./tests/smtlib2_files/kapurEUFExample2.smt2 f
#	gdb --args ./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 f
#	gdb --args ./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 y$1
#	gdb --args ./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2 f
#	gdb --args ./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2 f

valgrind : euf_interpolator
	valgrind ./euf_interpolator ./tests/smtlib2_files/kapurEUFExample.smt2 v
#	valgrind ./euf_interpolator ./tests/smtlib2_files/simple.smt2 f 
#	valgrind ./euf_interpolator ./tests/smtlib2_files/simple2.smt2 f
#	valgrind ./euf_interpolator ./tests/smtlib2_files/simple2.smt3 f
#	valgrind ./euf_interpolator ./tests/smtlib2_files/three_arguments.smt2 f
#	valgrind ./euf_interpolator ./tests/smtlib2_files/three_arguments2.smt2 f
#	valgrind ./euf_interpolator ./tests/smtlib2_files/three_arguments3.smt2 f
#	valgrind ./euf_interpolator ./tests/smtlib2_files/kapurEUFExample2.smt2 f
#	valgrind ./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 f
#	valgrind ./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2 y$1
#	valgrind ./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2 f
#	valgrind ./euf_interpolator /home/jose/Downloads/QF_UF-master/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2 f

.PHONY: clean
clean:
	rm -rf $(ODIR)/* euf_interpolator
