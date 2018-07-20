Z3DIR=~/Documents/Applications/z3/
IDIR = ./include/
ODIR = ./obj/
SDIR = ./src/
CC = g++
CFLAGS = -I$(IDIR) -I$(Z3DIR)src/api -I$(Z3DIR)src/api/c++ -std=c++11

SRC=$(wildcard $(SDIR)*.cpp)
OBJS=$(patsubst $(SDIR)%.cpp, $(ODIR)%.o, $(SRC))
DEPS=$(wildcard $(IDIR)*.h)

all: main

$(ODIR)%.o: $(SDIR)%.cpp $(DEPS)
	$(CC) -c -o $@ $< -I$(SDIR) $(CFLAGS) 
main: $(OBJS) $(Z3DIR)/build/libz3.dylib
	$(CC) -o $@ $^ $(Z3DIR)/build/libz3.dylib -lpthread
test_old:
	for x in ./tests/old/*; do\
		./main $$x; \
	done
.PHONY: clean
clean:
	rm $(ODIR)*
