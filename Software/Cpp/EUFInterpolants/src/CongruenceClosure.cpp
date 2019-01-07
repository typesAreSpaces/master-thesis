#include "CongruenceClosure.h"

bool traceMerge = false;
bool traceCombine = false;
bool tracePending = false;
bool traceEC = false;
bool traceSigTable = false;

void CongruenceClosure::init(Z3_context c){
  unsigned lhs, rhs;
  Vertex * lhsVertex, * rhsVertex;
  for(std::vector<std::pair<Z3_ast, Z3_ast> >::iterator it = equations.begin();
      it != equations.end(); ++it){
    lhs = Z3_get_ast_id(c, it->first);
    rhs = Z3_get_ast_id(c, it->second);
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
			std::cout << EC << std::endl;
      std::cout << "==========================================" << std::endl;
    }
  }
}

CongruenceClosure::CongruenceClosure(Z3_context c, Z3_ast v, std::set<std::string> & symbolsToElim) :
  SignatureTable(c, v, symbolsToElim) {
  init(c);
}

CongruenceClosure::CongruenceClosure(Z3_context c, Z3_ast v) :
  SignatureTable(c, v) {
  init(c);
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
			std::cout << EC << std::endl;
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
					std::cout << (*it)->to_string() << " and " << std::endl;
					std::cout << _temp->to_string() << std::endl;
					std::cout << "==========================================" << std::endl;
				}
      }
      catch (const char * msg){
				enter(*it);
				if(traceSigTable){
					std::cout << "==========================================" << std::endl;
					std::cout << "Current Signature Table" << std::endl;
					std::cout << *dynamic_cast<SignatureTable*>(this) << std::endl;
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

bool CongruenceClosure::checkCorrectness(){
  unsigned totalNumVertex = Vertex::getTotalNumVertex();

  for(unsigned i = 0; i < totalNumVertex - 1; ++i)
    for(unsigned j = i + 1; j < totalNumVertex; ++j){
      Vertex * u = getTerm(i), * v = getTerm(j);
      if(u->getArity() == v->getArity()){
				if(u->getArity() == 1
					 && getSignatureArg1(u) == getSignatureArg1(v)
					 && find(u)->getId() != find(v)->getId())
						return false;
				if(u->getArity() == 2
					 && getSignatureArg2(u) == getSignatureArg2(v)
					 && find(u)->getId() != find(v)->getId())
					return false;
      }
    }
  return true;
}

std::ostream & operator << (std::ostream & os, CongruenceClosure & cc){
  os << "Congruence Closure" << std::endl;
  unsigned totalNumVertex = Vertex::getTotalNumVertex();
  
  for(unsigned i = 0; i < totalNumVertex; ++i){
    // Just print non-extra nodes
		auto term = cc.getTerm(i);
    if(term->getName()[0] != '_')
      os << "Vertex: " << term->to_string()
				 << " Representative: " << cc.find(term)->to_string() << std::endl;
	}
  return os;
}
