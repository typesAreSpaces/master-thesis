include config.mk
FILE=main.cpp
TESTFILE=test.cpp
TDIR=~/Documents/QF_UF
TESTS=$(wildcard $(TDIR)/*/*.smt2)

all: main 
main$(OBJ_EXT): ./$(FILE)
	$(CXX) $(CXXFLAGS) $(OS_DEFINES) $(EXAMP_DEBUG_FLAG) $(CXX_OUT_FLAG)main$(OBJ_EXT) $(LINK_FLAGS) -I$(PREFIX)/src/api -I$(PREFIX)/src/api/c++ ./$(FILE)
main: $(PREFIX)/build/libz3$(SO_EXT) main$(OBJ_EXT)
	$(CXX) $(LINK_OUT_FLAG)main$(EXE_EXT) $(LINK_FLAGS) main$(OBJ_EXT)  $(PREFIX)/build/libz3$(SO_EXT) $(LINK_EXTRA_FLAGS)

test$(OBJ_EXT): ./$(TESTFILE)
	$(CXX) $(CXXFLAGS) $(OS_DEFINES) $(EXAMP_DEBUG_FLAG) $(CXX_OUT_FLAG)test$(OBJ_EXT) $(LINK_FLAGS) -I$(PREFIX)/src/api -I$(PREFIX)/src/api/c++ ./$(TESTFILE)
build_test: $(PREFIX)/build/libz3$(SO_EXT) test$(OBJ_EXT)
	$(CXX) $(LINK_OUT_FLAG)test$(EXE_EXT) $(LINK_FLAGS) test$(OBJ_EXT)  $(PREFIX)/build/libz3$(SO_EXT) $(LINK_EXTRA_FLAGS)

run_test: $(TESTS)
	./test $^

clean:
	rm -f *.o
run:
	./main
