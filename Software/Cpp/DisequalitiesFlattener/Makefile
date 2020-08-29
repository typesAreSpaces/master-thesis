Z3DIR = /home/jose/Documents/GithubProjects/z3__
Z3EXT = so

SRC = $(wildcard *.cpp)
OBJS = $(patsubst %.cpp, %.o, $(SRC)) $(Z3DIR)/build/libz3.$(Z3EXT) 
DEPS = $(wildcard *.h)

main: $(OBJS)
	g++ -o main $(OBJS)

%.o : %.cpp $(DEPS)
	g++ -c -o $@ $(FLAGS) $< 

.PHONY: clean
clean:
	rm -rf *.o

