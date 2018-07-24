Z3DIR=/Users/joseabelcastellanosjoo/Documents/Applications/z3
IDIR = ./include
ODIR = ./obj
SDIR = ./src
CC = g++
FLAGS = -I$(SDIR)/ -I$(IDIR)/ -I$(Z3DIR)/src/api -I$(Z3DIR)/src/api/c -I$(Z3DIR)/src/api/c++ -std=c++11
CXXFLAGS= -D_MP_INTERNAL -D_AMD64_ -DNDEBUG -D_EXTERNAL_RELEASE  -fvisibility=hidden -c -mfpmath=sse -msse -msse2 -D_NO_OMP_ -O3 -D _EXTERNAL_RELEASE \
-fomit-frame-pointer -Wno-unknown-pragmas -Wno-overloaded-virtual -Wno-unused-value -fPIC

SRC=$(wildcard $(SDIR)/*.cpp)
OBJS=$(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS=$(wildcard $(IDIR)/*.h)

all: main

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -c -o$@  $(FLAGS) $< 
main: $(OBJS) $(Z3DIR)/build/libz3.dylib
	$(CC) -o $@ $^ $(Z3DIR)/build/libz3.dylib -lpthread
test_old:
	for x in ./tests/old/*; do echo $$x; ./main $$x; done
test_smt2:
	for x in ./tests/smt2lib/*; do echo $$x; ./main $$x; done
.PHONY: clean
clean:
	rm $(ODIR)/* main
