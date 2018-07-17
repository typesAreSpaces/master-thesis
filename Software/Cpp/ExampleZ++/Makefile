include config.mk
IDIR=./include/
ODIR=./obj/
SDIR=./src/
SRC =$(wildcard $(SDIR)*.cpp)
OBJS=$(patsubst $(SDIR)%.cpp, $(ODIR)%.o, $(SRC))
DEPS=$(wildcard $(IDIR)*.h)
TESTS=$(wildcard ~/Documents/QF_UF/*/*.smt2)

all: main

$(ODIR)%$(OBJ_EXT): $(SDIR)%.cpp $(DEPS)
	$(CXX) $(CXXFLAGS) $(OS_DEFINES) $(EXAMP_DEBUG_FLAG) $(CXX_OUT_FLAG)$@ $(LINK_FLAGS) -I$(IDIR) -I$(PREFIX)/src/api -I$(PREFIX)/src/api/c -I$(PREFIX)/src/api/c++ $<

main: $(OBJS) $(PREFIX)/build/libz3$(SO_EXT)
	$(LINK) $(LINK_OUT_FLAG)$@$(EXE_EXT) $(LINK_FLAGS) $^  $(PREFIX)/build/libz3$(SO_EXT) $(LINK_EXTRA_FLAGS)

run_test: $(TESTS)
	./main $^

.PHONY: clean

clean:
	rm -f $(ODIR)*.o


