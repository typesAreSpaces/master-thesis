#include <iostream>
#include <fstream>
#include <string>
#include "unionfind.hpp"
#include "node.hpp"
#include "signatureTable.hpp"
#include "congruenceClosure.hpp"

bool debugPrint = false;
bool performanceCheck = false;

UF initializeUF(int & numTerms, int & numEqs, term & terms, std::string fileName){
  int lhs, rhs, fname, fargs, fnumargs;
  std::ifstream file ("tests/" + fileName);
  file >> numTerms;
  file >> numEqs;
  if(performanceCheck)
    std::cout << "Input File:\n";
  UF uf = UF(numTerms);

  for(int i = 0; i < numTerms; ++i){
    terms.push_back(linkedList());
    file >> fname;
    terms[i].add(fname);
    file >> fnumargs;
    if(performanceCheck){
      std::cout << fname << " ";
      std::cout << fnumargs << " ";
    }
    while(fnumargs > 0){
      file >> fargs;
      if(performanceCheck)
	std::cout << fargs << " ";
      terms[i].add(fargs);
      --fnumargs;
    }
    if(performanceCheck)
      std::cout << std::endl;
    uf.setPreds(terms[i]);
  }
  
  for(int i = 0; i < numEqs; ++i){
    file >> lhs;
    file >> rhs;
    circularList predLHS = uf.list(uf.find(lhs)), predRHS = uf.list(uf.find(rhs));
    int l1 = predLHS.size(), l2 = predRHS.size();
    if(debugPrint)
      std::cout << "Merging during equational process: " << lhs << " " << l1 << " " << rhs << " " << l2 << std::endl;
    if(l1 >= l2){
      uf.merge(lhs, rhs, l1, l2);
      uf.mergeCircularList(uf.find(lhs), predRHS);
    }
    else{
      uf.merge(rhs, lhs, l2, l1);
      uf.mergeCircularList(uf.find(rhs), predLHS);
    }
  }
  file.close();  
  return uf;
}

void congruenceClosureAlgorithm(term & terms, int numTerms, UF & uf, signatureTable & sigTable){
  setSingleton pending;
  setPair combine;
  for(term::iterator it = terms.begin(); it != terms.end(); ++it){
    // Only add functional symbols with arity > 0
    if(it->size() > 1)
      pending.insert(it->getList()->data);
    if(debugPrint){
      std::cout << "Printing Predecessors of " << it->getList()->data << std::endl;  
      uf.list(uf.find(it->getList()->data)).print();
      std::cout << std::endl;
    }
  }
  
  while(!pending.empty()){
    combine.clear();
    for(setSingleton::iterator it = pending.begin(); it != pending.end(); ++it){
      linkedList tempLL = terms[*it];
      // We need to update signatures
      // using the unionfind Data Structure
      if(tempLL.size() == 2){
	tempLL.head->next->data = uf.find(tempLL.head->next->data);
      }
      if(tempLL.size() == 3){
	tempLL.head->next->data = uf.find(tempLL.head->next->data);
	tempLL.head->next->next->data = uf.find(tempLL.head->next->next->data);
      }
      if(debugPrint){
	std::cout << "From pending\n";
	tempLL.print();
	std::cout << std::endl;
      }
      //int tempV = sigTable.query(tempLL);
      int tempV = sigTable.query(terms[*it]);
      if(debugPrint){
	std::cout << "From pending (original)\n";
	terms[*it].print();
	std::cout << std::endl;
      }
      if(tempV == -1){
	sigTable.enter(tempLL);
	if(debugPrint){
	  std::cout << "Inserting to the SigTable\n";
	  tempLL.print();
	  std::cout << std::endl;
	}
      }
      else{
	combine.insert(std::make_pair(*it, tempV));
	if(debugPrint){
	  std::cout << "Inserting to combine\n";
	  std::cout << *it << " " << tempV << std::endl;
	}
      }
    }
    
    pending.clear();
    for(setPair::iterator it = combine.begin(); it != combine.end(); ++it){
      if(uf.find(it->first) != uf.find(it->second)){
	if(debugPrint){
	  std::cout << "From combine\n";
	  std::cout << "(" << it->first << ", " << it->second << ")" << std::endl;
	  std::cout << "(" << uf.find(it->first) << ", " << uf.find(it->second) << ")" << std::endl;
	  std::cout << std::endl;	
	}
	
	circularList listFirst = uf.list(uf.find(it->first));
	circularList listSecond = uf.list(uf.find(it->second));
	if(debugPrint){
	  std::cout << "First List (original)\n";
	  uf.list(it->first).print();
	  std::cout << std::endl;
	  std::cout << "First List (representative)\n";
	  listFirst.print();
	  std::cout << std::endl;
	  std::cout << "Second List (original)\n";
	  uf.list(it->second).print();
	  std::cout << std::endl;
	  std::cout << "Second List (representative)\n";
	  listSecond.print();
	  std::cout << std::endl;
	}
	int l1 = listFirst.size(), l2 = listSecond.size();
	if(l1 < l2){
	  if(l1 > 0){
	    node * tempIterator = listFirst.tail->next;
	    do{
	      sigTable.remove(terms[tempIterator->data]);
	      if(debugPrint){
		std::cout << "Inserting to pending\n";
		std::cout << tempIterator->data << std::endl;
	      }
	      pending.insert(tempIterator->data);
	      uf.addPred(uf.find(it->second), tempIterator->data);
	      
	      tempIterator = tempIterator->next;
	    } while(tempIterator != listFirst.tail->next);	    
	  }
	  uf.merge(uf.find(it->second), uf.find(it->first), l2, l1);
	}
	else{
	  if(l2 > 0){
	    node * tempIterator = listSecond.tail->next;
	    do{
	      sigTable.remove(terms[tempIterator->data]);
	      if(debugPrint){
		std::cout << "Inserting to pending\n";
		std::cout << tempIterator->data << std::endl;
	      }
	      pending.insert(tempIterator->data);
	      uf.addPred(uf.find(it->first), tempIterator->data);
	      
	      tempIterator = tempIterator->next;	      
	    } while(tempIterator != listSecond.tail->next);	    
	  }
	  uf.merge(uf.find(it->first), uf.find(it->second), l1, l2);
	}
      }
    }    
  }
}
