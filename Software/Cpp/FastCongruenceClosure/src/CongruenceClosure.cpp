#include "CongruenceClosure.h"

bool traceMerge = false;
bool traceCombine = false;
bool tracePending = false;
bool traceEC = false;
bool traceSigTable = false;

CongruenceClosure::CongruenceClosure(GTerms & terms, SignatureTable & sigTable, std::istream & in) :
  terms(terms), sigTable(sigTable) {
  int numEq, lhs, rhs;
  Vertex * lhsVertex, *rhsVertex;
  in >> numEq;
  for(int i = 0; i < numEq; ++i){
    in >> lhs >> rhs;
    lhsVertex = terms.getTerm(lhs);
    rhsVertex = terms.getTerm(rhs);
    
    if(lhsVertex->getLength() < rhsVertex->getLength()){
      terms.merge(terms.getTerm(rhs), terms.getTerm(lhs));
      if(traceMerge){
	std::cout << "==========================================" << std::endl;
	std::cout << "Merging " << std::endl;
	std::cout << lhsVertex->to_string() << std::endl;
	std::cout << " to " << std::endl;
	std::cout << rhsVertex->to_string() << std::endl;
	std::cout << "==========================================" << std::endl;
      }
    }
    else{
      terms.merge(terms.getTerm(lhs), terms.getTerm(rhs));
      if(traceMerge){
	std::cout << "==========================================" << std::endl;
	std::cout << "Merging " << std::endl;
	std::cout << rhsVertex->to_string() << std::endl;
	std::cout << " to " << std::endl;
	std::cout << lhsVertex->to_string() << std::endl;
	std::cout << "==========================================" << std::endl;
      }
    }
    if(traceEC){
      std::cout << "==========================================" << std::endl;
      std::cout << "Terms and ID's" << std::endl;
      for(int i = 0; i < Vertex::getTotalNumVertex(); ++i)
	std::cout << i << " " << terms.getTerm(i)->to_string() << std::endl;
      std::cout << "==========================================" << std::endl;
      std::cout << "==========================================" << std::endl;
      std::cout << "Current Equivalence Class" << std::endl;
      terms.getEC().print(std::cout);
      std::cout << "==========================================" << std::endl;
    }
  }
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
	if(traceCombine){
	  std::cout << "==========================================" << std::endl;
	  std::cout << "Inserting to Combine" << std::endl;
	  std::cout << (*it)->to_string() << "and " << std::endl;
	  std::cout << _temp->to_string() << std::endl;
	  std::cout << "==========================================" << std::endl;
	}
      }
      catch (const char * msg){
	sigTable.enter(*it);
	if(traceSigTable){
	  std::cout << "==========================================" << std::endl;
	  std::cout << "Current Signature Table" << std::endl;
	  sigTable.print(std::cout);
	  std::cout << "==========================================" << std::endl;
	}
      }
    }
    pending.clear();
    for(Combine::iterator it = combine.begin(); it != combine.end(); ++it){
      Vertex * v = it->first, * w = it->second, * findV = terms.find(v), * findW = terms.find(w);
      if(findV->getId() != findW->getId()){
	if(findV->getLength() < findW->getLength()){
	  CircularList<int> * listFindV = findV->getPredecessors();
	  if(findV->getLength() != 0){
	    CircularList<int>::iterator it = listFindV->begin();
	    do{
	      Vertex * u = terms.getTerm((*it).data);
	      sigTable.remove(u);
	      pending.insert(u);
	      ++it;
	    } while(it != listFindV->begin());
	  }
	  if(traceMerge){
	    std::cout << "==========================================" << std::endl;
	    std::cout << "Merging " << std::endl;
	    std::cout << findW->to_string() << std::endl;
	    std::cout << " to " << std::endl;
	    std::cout << findV->to_string() << std::endl;
	    std::cout << "==========================================" << std::endl;
	  }
	  terms.merge(findW, findV);
	}
	else{
	  CircularList<int> * listFindW = findW->getPredecessors();
	  if(findW->getLength() != 0){
	    CircularList<int>::iterator it = listFindW->begin();
	    do{
	      Vertex * u = terms.getTerm((*it).data);
	      sigTable.remove(u);
	      pending.insert(u);
	      ++it;
	    } while(it != listFindW->begin());
	  }
	  if(traceMerge){
	    std::cout << "==========================================" << std::endl;
	    std::cout << "Merging " << std::endl;
	    std::cout << findW->to_string() << std::endl;
	    std::cout << " to " << std::endl;
	    std::cout << findV->to_string() << std::endl;
	    std::cout << "==========================================" << std::endl;
	  }
	  terms.merge(findV, findW);
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
