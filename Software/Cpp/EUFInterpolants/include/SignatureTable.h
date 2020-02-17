#ifndef SIG_TABLE_H
#define SIG_TABLE_H

#include <utility>
#include <unordered_map>
#include "Signature.h"
#include "Terms.h"

typedef std::unordered_map<UnarySignature, Term*, UnarySignature::Hash> UnaryTerms;
typedef std::unordered_map<BinarySignature, Term*, BinarySignature::Hash> BinaryTerms; 

class SignatureTable {
public:
  SignatureTable();
  ~SignatureTable();
  void enter(Term*, UnionFind &);
  void remove(Term*, UnionFind &);
  Term* query(Term*, UnionFind &);
  UnarySignature getUnarySignature(Term*, UnionFind &);
  BinarySignature getBinarySignature(Term*, UnionFind &);
  friend std::ostream & operator << (std::ostream &, const SignatureTable &);
 protected:
  UnaryTerms unaryTable;
  BinaryTerms binaryTable;
};

#endif
