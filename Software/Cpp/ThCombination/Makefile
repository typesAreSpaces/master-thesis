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
FLAGS = -I$(SDIR) -I$(IDIR) -std=c++11 -Wall -DDISJ_EQS_PROPAGATOR_NO_AB_MIXED_EQS -DADD_COMMON_PREFIX
#FLAGS = -I$(SDIR) -I$(IDIR) -std=c++11 -Wall

SRC = $(wildcard $(SDIR)/*.cpp)
OBJS = $(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC)) $(Z3DIR)/build/libz3.$(Z3EXT) 
DEPS = $(wildcard $(IDIR)/*.h)

# ------------------------------------------------------------------------------------------
#  Build

#all: tests/disj_eqs_propagator_test
#all: tests/cdcl_t_test
#all: tests/res_proof_test
#all: tests/proof_factory_test
all: tests/basic_test
#all: tests/smt_file_test
#all: tests/extensive_test

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@ $(FLAGS) $<

# ------------------------------------------------------------------------------------------
#  Tests
.PHONY: tests/res_proof_test
tests/res_proof_test: $(OBJS) 
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@
	rm -rf tests/*.o $@

.PHONY: tests/proof_factory_test
tests/proof_factory_test: $(OBJS) 
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@
	rm -rf tests/*.o $@

.PHONY: tests/cdcl_t_test
tests/cdcl_t_test: $(OBJS) # Done 
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@
	rm -rf tests/*.o $@

.PHONY: tests/disj_eqs_propagator_test
tests/disj_eqs_propagator_test: $(OBJS) # Done
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@
	rm -rf tests/*.o $@

.PHONY: tests/basic_test
tests/basic_test: $(OBJS)
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@
	rm -rf tests/*.o $@

.PHONY: tests/smt_file_test
tests/smt_file_test: $(OBJS)
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	#./$@ ./tests/smt2-files/example.smt2
	#./$@ ./tests/smt2-files/example1_reduced_z3.smt2
	./$@ ./tests/smt2-files/test1.smt2
	rm -rf tests/*.o $@

.PHONY: tests/extensive_test
tests/extensive_test: $(OBJS)
	$(CC) -g -c -o ./$@.o $(FLAGS) ./$@.cpp
	$(CC) -g -o $@ $(OBJS) ./$@.o -lpthread -Wall
	./$@ ./tests/smt2-files/part_a_goals.smt2 ./tests/smt2-files/part_b_goals.smt2
	rm -rf tests/*.o $@


# ------------------------------------------------------------------------------------------

parser:
	make -C ../z3-proofs2latex

print_proof: ../z3-proofs2latex/z3-proof-parser-sexpr thcombination
	./thcombination > $@.txt
	$^ < $@.txt > $@.tex
	pdflatex $@.tex

.PHONY: clean_proof
clean_proof:
	rm print_proof*

.PHONY: clean
clean:
	rm -rf $(ODIR)/* proof proof-temp file.cnf
