#ifndef SIG_TABLE_H
#define SIG_TABLE_H

#include<iostream>
#include <utility>
#include <unordered_map>
#include "Vertex.h"
#include "Signature.h"
#include "GTerms.h"

typedef std::unordered_map<signatureArg1, Vertex*, signatureArg1::Hash> treeArg1;
typedef std::unordered_map<signatureArg2, Vertex*, signatureArg2::Hash> treeArg2; 

class SignatureTable{
private:
  treeArg1 table1;
  treeArg2 table2;
  GTerms & gterms;
public:
  SignatureTable(GTerms &);
  ~SignatureTable();
  void enter(Vertex*);
  void remove(Vertex*);
  Vertex* query(Vertex*);
  signatureArg1 getSignatureArg1(Vertex*);
  signatureArg2 getSignatureArg2(Vertex*);
  std::ostream & print(std::ostream &);
};

#endif