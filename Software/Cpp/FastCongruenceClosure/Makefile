Z3DIR=~/Documents/Applications/z3
IDIR = ./include
ODIR = ./obj
SDIR = ./src
CC = g++
FLAGS = -I$(IDIR)/ -I$(Z3DIR)/src/api -I$(Z3DIR)/src/api/c -I$(Z3DIR)/src/api/c++ 
CXXFLAGS= -D_MP_INTERNAL -D_AMD64_ -DNDEBUG -D_EXTERNAL_RELEASE  -fvisibility=hidden -c -mfpmath=sse -msse -msse2 -D_NO_OMP_ -O3 -D _EXTERNAL_RELEASE \
-fomit-frame-pointer -Wno-unknown-pragmas -Wno-overloaded-virtual -Wno-unused-value -fPIC

SRC=$(wildcard $(SDIR)/*.cpp)
OBJS=$(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
DEPS=$(wildcard $(IDIR)/*.h)

all: main

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) $(CXXFLAGS) -o $@ -I$(SDIR)/ $(FLAGS) $< 
main: $(OBJS) $(Z3DIR)/build/libz3.dylib
	$(CC) -o $@ $^ $(Z3DIR)/build/libz3.dylib -lpthread
test_old:
	for x in ./tests/old/*; do\
		./main $$x; \
	done
.PHONY: clean
clean:
	rm $(ODIR)/*
