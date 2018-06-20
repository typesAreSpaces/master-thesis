include config.mk
FILE=main.cpp

all: main run
main$(OBJ_EXT): ./$(FILE)
	$(CXX) $(CXXFLAGS) $(OS_DEFINES) $(EXAMP_DEBUG_FLAG) $(CXX_OUT_FLAG)main$(OBJ_EXT) $(LINK_FLAGS) -I$(PREFIX)/src/api -I$(PREFIX)/src/api/c++ ./$(FILE)
main: $(PREFIX)/build/libz3$(SO_EXT) main$(OBJ_EXT)
	$(CXX) $(LINK_OUT_FLAG)main$(EXE_EXT) $(LINK_FLAGS) main$(OBJ_EXT)  $(PREFIX)/build/libz3$(SO_EXT) $(LINK_EXTRA_FLAGS)
clean:
	rm -f *.o
run:
	./main
