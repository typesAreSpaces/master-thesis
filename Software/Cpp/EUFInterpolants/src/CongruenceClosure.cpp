#include "CongruenceClosure.h"

bool traceMerge = false;
bool traceCombine = false;
bool tracePending = false;
bool traceEC = false;
bool traceSigTable = false;

void CongruenceClosure::init(){
  unsigned lhs, rhs;
  Vertex * lhsVertex, *rhsVertex;
  for(std::vector<std::pair<unsigned, unsigned> >::iterator it = equations.begin();
      it != equations.end(); ++it){
    lhs = it->first;
    rhs = it->second;
    lhsVertex = getTerm(lhs);
    rhsVertex = getTerm(rhs);
    
    if(lhsVertex->getLength() < rhsVertex->getLength()){
      merge(getTerm(rhs), getTerm(lhs));
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
      merge(getTerm(lhs), getTerm(rhs));
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
      for(unsigned i = 0; i < Vertex::getTotalNumVertex(); ++i)
				std::cout << i << " " << getTerm(i)->to_string() << std::endl;
      std::cout << "==========================================" << std::endl;
      std::cout << "==========================================" << std::endl;
      std::cout << "Current Equivalence Class" << std::endl;
      EC.print(std::cout);
      std::cout << "==========================================" << std::endl;
    }
  }
}

CongruenceClosure::CongruenceClosure(Z3_context c, Z3_ast v, std::set<std::string> & symbolsToElim) :
  SignatureTable(c, v, symbolsToElim) {
  init();
}

CongruenceClosure::CongruenceClosure(Z3_context c, Z3_ast v) :
  SignatureTable(c, v) {
  init();
}

CongruenceClosure::CongruenceClosure(std::istream & in) : SignatureTable(in) {
  unsigned numEq, lhs, rhs;
  Vertex * lhsVertex, *rhsVertex;
  in >> numEq;
  for(unsigned i = 0; i < numEq; ++i){
    in >> lhs >> rhs;
    lhsVertex = getTerm(lhs);
    rhsVertex = getTerm(rhs);
    
    if(lhsVertex->getLength() < rhsVertex->getLength()){
      merge(getTerm(rhs), getTerm(lhs));
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
      merge(getTerm(lhs), getTerm(rhs));
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
      for(unsigned i = 0; i < Vertex::getTotalNumVertex(); ++i)
				std::cout << i << " " << getTerm(i)->to_string() << std::endl;
      std::cout << "==========================================" << std::endl;
      std::cout << "==========================================" << std::endl;
      std::cout << "Current Equivalence Class" << std::endl;
      EC.print(std::cout);
      std::cout << "==========================================" << std::endl;
    }
  }
}

CongruenceClosure::~CongruenceClosure(){}

void CongruenceClosure::algorithm(){
  Pending pending;
  Combine combine;
  unsigned totalNumVertex = Vertex::getTotalNumVertex();
  
  // Adding functional grounded vertices to pending
  for(unsigned i = 0; i < totalNumVertex; ++i){
    Vertex * _temp = getTerm(i);
    if(_temp->getArity() >= 1)
      pending.insert(_temp);
  }
  
  while(!pending.empty()){
    combine.clear();
    for(Pending::iterator it = pending.begin(); it != pending.end(); ++it){
      try{
				Vertex * _temp = query(*it);
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
				enter(*it);
				if(traceSigTable){
					std::cout << "==========================================" << std::endl;
					std::cout << "Current Signature Table" << std::endl;
					SignatureTable::print(std::cout);
					std::cout << "==========================================" << std::endl;
				}
      }
    }
    pending.clear();
    for(Combine::iterator it = combine.begin(); it != combine.end(); ++it){
      Vertex * v = it->first, * w = it->second, * findV = find(v), * findW = find(w);
      if(findV->getId() != findW->getId()){
				if(findV->getLength() < findW->getLength()){
					CircularList<unsigned> * listFindV = findV->getPredecessors();
					if(findV->getLength() != 0){
						CircularList<unsigned>::iterator it = listFindV->begin();
						do{
							Vertex * u = getTerm((*it).data);
							remove(u);
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
					merge(findW, findV);
				}
				else{
					CircularList<unsigned> * listFindW = findW->getPredecessors();
					if(findW->getLength() != 0){
						CircularList<unsigned>::iterator it = listFindW->begin();
						do{
							Vertex * u = getTerm((*it).data);
							remove(u);
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
					merge(findV, findW);
				}
      }
    }
  }
}

std::ostream & CongruenceClosure::print(std::ostream & os){
  os << "Congruence Closure:" << std::endl;
  unsigned totalNumVertex = Vertex::getTotalNumVertex();
  
  for(unsigned i = 0; i < totalNumVertex; ++i){
    // Just print non-extra nodes
    if(getTerm(i)->getName()[0] != '_')
      os << "Vertex: " << getTerm(i)->to_string() << std::endl << 
				"Representative: " << find(getTerm(i))->to_string() << std::endl;
  }
  
  os << std::endl;
  return os;
}

bool CongruenceClosure::checkCorrectness(){
  bool check = true;
  unsigned totalNumVertex = Vertex::getTotalNumVertex();

  for(unsigned i = 0; i < totalNumVertex - 1; ++i)
    for(unsigned j = i + 1; j < totalNumVertex; ++j){
      Vertex * u = getTerm(i), * v = getTerm(j);
      if(u->getArity() == v->getArity()){
				if(u->getArity() == 1){
					if(getSignatureArg1(u) == getSignatureArg1(v) && find(u)->getId() != find(v)->getId())
						check = false;
				}
				if(u->getArity() == 2)
					if(getSignatureArg2(u) == getSignatureArg2(v) && find(u)->getId() != find(v)->getId())
						check = false;
      }
    }
  return check;
}
