#include "congruenceClosure.h"

CongruenceClosure::CongruenceClosure(GTerms & terms, SignatureTable & sigTable, std::istream & in) :
  terms(terms), sigTable(sigTable) {
  int numEq, a, b;
  in >> numEq;
  for(int i = 0; i < numEq; ++i){
    in >> a >> b;
    terms.merge(terms.getTerm(a), terms.getTerm(b));
  }
  std::cout << "Terms: " << std::endl;
  terms.print(std::cout);
}

CongruenceClosure::~CongruenceClosure(){}

void CongruenceClosure::algorithm(){
  Pending pending;
  Combine combine;
  int totalNumVertex = Vertex::getTotalNumVertex();
  
  // Adding functional grounded vertices to pending
  for(int i = 0; i < totalNumVertex; ++i){
    Vertex * _temp = terms.getTerm(i);
    if(_temp->getArity() >= 1)
      pending.insert(_temp);
  }
  
  while(!pending.empty()){
    combine.clear();
    for(Pending::iterator it = pending.begin(); it != pending.end(); ++it){
      try{
	Vertex * _temp = sigTable.query(*it);
	combine.insert(std::make_pair(*it, _temp));
      }
      catch (const char * msg){
	sigTable.enter(*it);
      }
    }
    pending.clear();
    for(Combine::iterator it = combine.begin(); it != combine.end(); ++it){
      Vertex * v = it->first, * w = it->second, * findV = terms.find(v), * findW = terms.find(w);
      if(findV->getId() != findW->getId()){
	if(findV->getLength() < findW->getLength()){
	  CircularList<int> * listFindV = findV->getPredecessors();
	  // ==================================================
	  // Traversing the CircularList
	  // TODO: Implement an iterator for
	  // the CircularList class
	  if(findV->getLength() != 0){
	    node<int> * _temp = listFindV->getList()->next;
	    do{
	      Vertex * u = terms.getTerm(_temp->data);
	      sigTable.remove(u);
	      pending.insert(u);
	      _temp = _temp->next;
	    } while(_temp != listFindV->getList()->next);
	  }
	  // ==================================================
	}
	else{
	  CircularList<int> * listFindW = findW->getPredecessors();
	  // ==================================================
	  // Traversing the CircularList
	  // TODO: Implement an iterator for
	  // the CircularList class
	  if(findW->getLength() != 0){
	    node<int> * _temp = listFindW->getList()->next;
	    do{
	      Vertex * u = terms.getTerm(_temp->data);
	      sigTable.remove(u);
	      pending.insert(u);
	      _temp = _temp->next;
	    } while(_temp != listFindW->getList()->next);
	  }
	  // ==================================================
	}
      }
    }
  }
}

std::ostream & CongruenceClosure::print(std::ostream & os){
  os << "Congruence Closure:" << std::endl;
  int totalNumVertex = Vertex::getTotalNumVertex();
  for(int i = 0; i < totalNumVertex; ++i){
    os << "Vertex: " << terms.getTerm(i)->to_string() <<
      ", Representative: " << terms.find(terms.getTerm(i))->to_string() << std::endl; 
  }
  os << std::endl;
  return os;
}
