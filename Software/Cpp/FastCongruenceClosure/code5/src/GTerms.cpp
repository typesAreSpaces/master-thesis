#include "GTerms.h"

GTerms::GTerms(std::istream & in){
  int numTerms, _arity, _successor, mark;
  std::string _name;

  in >> numTerms;
  terms.resize(2*numTerms);
  additionalTerms.resize(numTerms);

  for(int i = 0; i < numTerms; ++i)
    terms[i] = new Vertex();

  // Adding {x_j | 0 <= j < n} vertices
  // where n is the number of original vertices
  for(int i = 0; i < numTerms; ++i){
    terms[numTerms + i] = new Vertex("x" + std::to_string(i), 0);
    additionalTerms[i] = terms[numTerms + i];
  }

  for(int i = 0; i < numTerms; ++i){
    in >> _name >> _arity;
    terms[i]->setName(_name);
    if(_arity >= 2){
      mark = terms.size();
      terms[i]->setArity(2);
      // Adding w_j(v) vertices
      for(int j = 2; j <= _arity; ++j){
	Vertex * temp = new Vertex("w" + std::to_string(j) + std::to_string(terms[i]->getId()), 2);
	terms.push_back(temp);
	additionalTerms.push_back(temp);
      }
      in >> _successor;
      terms[i]->addSuccessor(terms[_successor]);
      terms[i]->addSuccessor(terms[mark]);
      for(int j = 0; j < _arity - 2; ++j){
	in >> _successor;
	terms[mark + j]->addSuccessor(terms[_successor]);
	terms[mark + j]->addSuccessor(terms[mark + j + 1]);
      }
      in >> _successor;
      terms[mark + _arity - 2]->addSuccessor(terms[_successor]);
      terms[mark + _arity - 2]->addSuccessor(terms[numTerms + _arity]);
    }
    else{
      terms[i]->setArity(_arity);
      for(int j = 0; j < _arity; ++j){
	in >> _successor;       
	terms[i]->addSuccessor(terms[_successor]);
      }
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
  /*
  std::cout << "OK done" << std::endl;
  for(std::vector<Vertex*>::iterator it = additionalTerms.begin(); it != additionalTerms.end(); ++it)
    os << **it << std::endl;
  */
  return os;
}
