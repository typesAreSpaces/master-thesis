#include "GTerms.h"

GTerms::GTerms(std::istream & in){
  int numTerms, _arity, _successor;
  std::string _name;
  in >> numTerms;
  terms.resize(numTerms);
  for(int i = 0; i < numTerms; ++i)
    terms[i] = new Vertex();
  for(int i = 0; i < numTerms; ++i){
    in >> _name >> _arity;
    terms[i]->setName(_name), terms[i]->setArity(_arity);
    for(int j = 0; j < _arity; ++j){
      in >> _successor;
      terms[i]->addSuccessor(terms[_successor]);
    }
  }
}
GTerms::~GTerms(){
  for(std::vector<Vertex*>::iterator it = terms.begin();
      it != terms.end(); ++it)
    delete *it;
}

std::ostream & GTerms::print(std::ostream & os){
  for(std::vector<Vertex*>::iterator it = terms.begin(); it != terms.end(); ++it)
    os << **it << std::endl;
  return os;
}
