#include <iostream>
#include <fstream>
#include <string>
#include "unionfind.hpp"
#include "node.hpp"
#include "signatureTable.hpp"
#include "congruenceClosure.hpp"

UF initializeUF(int & numTerms, int & numEqs, term & terms, std::string fileName){
  int lhs, rhs, fname, fargs, fnumargs;
  std::ifstream file ("tests/" + fileName);
  file >> numTerms;
  file >> numEqs;
  std::cout << "Input File:\n";
  UF uf = UF(numTerms);
  for(int i = 0; i < numTerms; ++i){
    terms.push_back(linkedList());
    file >> fname;
    std::cout << fname << " ";
    terms[i].add(fname);
    file >> fnumargs;
    std::cout << fnumargs << " ";
    while(fnumargs > 0){
      file >> fargs;
      std::cout << fargs << " ";
      terms[i].add(fargs);
      --fnumargs;
    }
    std::cout << std::endl;
    uf.setPreds(terms[i]);
  }
  
  for(int i = 0; i < numEqs; ++i){
    file >> lhs;
    file >> rhs;
    uf.merge(lhs, rhs, 0, 0);
    if(uf.getRank(lhs) > uf.getRank(rhs)){
      circularList tempCL = uf.list(rhs);
      if(tempCL.size() > 0){
	node * temp = tempCL.tail->next;
	do {
	  uf.addPred(uf.find(lhs), temp->data);
	  temp = temp->next;
	} while(temp != tempCL.tail->next);
      }
    }
    else{
      circularList tempCL = uf.list(lhs);
      if(tempCL.size() > 0){
	node * temp = tempCL.tail->next;
	do {
	  uf.addPred(uf.find(rhs), temp->data);
	  temp = temp->next;
	} while(temp != tempCL.tail->next);
      }
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
      int tempV = sigTable.query(tempLL);
      if(tempV == -1)
	sigTable.enter(tempLL);
      else
	combine.insert(std::make_pair(*it, tempV));
    }
    pending.clear();
    for(setPair::iterator it = combine.begin(); it != combine.end(); ++it){
      if(uf.find(it->first) != uf.find(it->second)){
	circularList listFirst = uf.list(uf.find(it->first));
	circularList listSecond = uf.list(uf.find(it->second));
	int l1 = listFirst.size(), l2 = listSecond.size();
	if(l1 < l2){
	  if(l1 > 0){
	    node * tempIterator = listFirst.tail->next;
	    do{
	      sigTable.remove(terms[tempIterator->data]);
	      pending.insert(tempIterator->data);
	      tempIterator = tempIterator->next;
	      uf.addPred(uf.find(it->second), tempIterator->data);
	    } while(tempIterator != listFirst.tail->next);	    
	  }
	  uf.merge(uf.find(it->second), uf.find(it->first), l2, l1);
	}
	else{
	  if(l2 > 0){
	    node * tempIterator = listSecond.tail->next;
	    do{
	      sigTable.remove(terms[tempIterator->data]);
	      pending.insert(tempIterator->data);
	      tempIterator = tempIterator->next;
	      uf.addPred(uf.find(it->first), tempIterator->data);
	    } while(tempIterator != listSecond.tail->next);	    
	  }
	  uf.merge(uf.find(it->first), uf.find(it->second), l1, l2);
	}
      }
    }    
  }
}
