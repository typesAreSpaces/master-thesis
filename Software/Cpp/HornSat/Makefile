IDIR=./include
SDIR=./src
ODIR=./obj
CC=g++
DEPS=$(wildcard $(IDIR)/*.h)
SRC=$(wildcard $(SDIR)/*.cpp)
OBJS=$(patsubst $(SDIR)/%.cpp, $(ODIR)/%.o, $(SRC))
CFLAGS= -I$(IDIR)

all: hornsat

$(ODIR)/%.o: $(SDIR)/%.cpp $(DEPS)
	$(CC) -g -c -o $@ $< $(CFLAGS)

hornsat: $(OBJS)
	$(CC) -g -o $@ $^

run: hornsat
	./hornsat

.PHONY: clean
clean:
	rm -rf $(ODIR)/*.o ./*\~ hornsat

test:
	for test in $(TESTS); do\
		echo 'Test: '$$test; \
		./hornsat < $$test; \
	done
