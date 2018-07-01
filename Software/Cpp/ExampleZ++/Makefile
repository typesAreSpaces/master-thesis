include config.mk
TESTS=$(wildcard ~/Documents/QF_UF/*/*.smt2)
SRC =$(wildcard ./*.cpp)

all: main test

%$(OBJ_EXT): ./%.cpp
	$(CXX) $(CXXFLAGS) $(OS_DEFINES) $(EXAMP_DEBUG_FLAG) $(CXX_OUT_FLAG)$@ $(LINK_FLAGS) -I$(PREFIX)/src/api -I$(PREFIX)/src/api/c++ $<

main: main$(OBJ_EXT) $(PREFIX)/build/libz3$(SO_EXT)
	$(LINK) $(LINK_OUT_FLAG)$@$(EXE_EXT) $(LINK_FLAGS) $^  $(PREFIX)/build/libz3$(SO_EXT) $(LINK_EXTRA_FLAGS)

test: test$(OBJ_EXT) $(PREFIX)/build/libz3$(SO_EXT)
	$(LINK) $(LINK_OUT_FLAG)$@$(EXE_EXT) $(LINK_FLAGS) $^  $(PREFIX)/build/libz3$(SO_EXT) $(LINK_EXTRA_FLAGS)

run_main: main
	./main

run_test: $(TESTS)
	./test $^

.PHONY: clean

clean:
	rm -f *.o *\~


