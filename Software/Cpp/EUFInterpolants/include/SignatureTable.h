#ifndef SIG_TABLE_H
#define SIG_TABLE_H

#include <utility>
#include <unordered_map>
#include "Signature.h"
#include "Terms.h"

typedef std::unordered_map<signatureArg1, Vertex*, signatureArg1::Hash> treeArg1;
typedef std::unordered_map<signatureArg2, Vertex*, signatureArg2::Hash> treeArg2; 

class SignatureTable : public Terms {
protected:
  treeArg1 table1;
  treeArg2 table2;
public:
  SignatureTable(Z3_context, Z3_ast);
  SignatureTable(Z3_context, Z3_ast, std::set<std::string> &);
  SignatureTable(std::istream &);
  ~SignatureTable();
  void enter(Vertex*);
  void remove(Vertex*);
  Vertex* query(Vertex*);
  signatureArg1 getSignatureArg1(Vertex*);
  signatureArg2 getSignatureArg2(Vertex*);
  friend std::ostream & operator << (std::ostream &, SignatureTable &);
};

#endif
