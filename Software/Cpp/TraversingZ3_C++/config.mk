PREFIX=~/Documents/Applications/z3
CC=gcc
CXX=g++
CXXFLAGS= -D_MP_INTERNAL -D_AMD64_ -DNDEBUG -D_EXTERNAL_RELEASE  -fvisibility=hidden -c -mfpmath=sse -msse -msse2 -D_NO_OMP_ -O3 -D _EXTERNAL_RELEASE \
-fomit-frame-pointer -Wno-unknown-pragmas -Wno-overloaded-virtual -Wno-unused-value -fPIC
EXAMP_DEBUG_FLAG=
CXX_OUT_FLAG=-o
OBJ_EXT=.o
LIB_EXT=.a
AR=ar
AR_FLAGS=rcs
AR_OUTFLAG=
EXE_EXT=
LINK=g++
LINK_FLAGS=
LINK_OUT_FLAG=-o
LINK_EXTRA_FLAGS=-lpthread
SO_EXT=.dylib
SLINK=g++
SLINK_FLAGS=-dynamiclib
SLINK_EXTRA_FLAGS=
SLINK_OUT_FLAG=-o
OS_DEFINES=
