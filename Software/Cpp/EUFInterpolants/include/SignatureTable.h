#ifndef SIG_TABLE_H
#define SIG_TABLE_H

#include <utility>
#include <unordered_map>
#include "Signature.h"
#include "Terms.h"

typedef std::unordered_map<UnarySignature, Term*, UnarySignature::Hash> UnaryTerms;
typedef std::unordered_map<BinarySignature, Term*, BinarySignature::Hash> BinaryTerms; 

class SignatureTable : public Terms {
protected:
  UnaryTerms unaryTable;
  BinaryTerms binaryTable;
	
public:
  SignatureTable(Z3_context, Z3_ast);
  SignatureTable(Z3_context, Z3_ast, std::set<std::string> &);
  ~SignatureTable();
  void enter(Term*);
  void remove(Term*);
  Term* query(Term*);
  UnarySignature getUnarySignature(Term*);
  BinarySignature getBinarySignature(Term*);
  friend std::ostream & operator << (std::ostream &, const SignatureTable &);
};

#endif
