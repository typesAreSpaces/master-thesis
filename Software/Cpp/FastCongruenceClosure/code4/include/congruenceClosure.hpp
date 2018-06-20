#ifndef CONG_CLOSURE
#define CONG_CLOSURE

#include "unionfind.hpp"
#include "signatureTable.hpp"
#include <string>
#include <set>

typedef std::vector<linkedList> term;
typedef std::set<int> setSingleton;
typedef std::set<std::pair<int, int> > setPair;

UF initializeUF(int &, int &, term &, std::string);
void congruenceClosureAlgorithm(term & , int , UF &, signatureTable &);

#endif
