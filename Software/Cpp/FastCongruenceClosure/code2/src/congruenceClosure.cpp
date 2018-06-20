#include <iostream>
#include <fstream>
#include <string>
#include "unionfind.hpp"
#include "node.hpp"
#include "signatureTable.hpp"
#include "congruenceClosure.hpp"

UF initializeUF(int & numTerms, int & numEqs, term & terms, funcName & funcNames, std::string fileName){
  int lhs, rhs, id, fname, fargs, fnumargs;
  std::ifstream file ("tests/" + fileName);
  file >> numTerms;
  file >> numEqs;
  funcNames.resize(numTerms);
  std::cout << "Input File:\n";
  UF uf = UF(numTerms);
  for(int i = 0; i < numTerms; ++i){
    terms.push_back(linkedList());
    file >> id >> fname;
    funcNames[id] = fname;
    std::cout << id << " " << fname << " ";
    terms[i].add(fname);
    terms[i].add(id);
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
    if(uf.list(uf.find(lhs)).size() > uf.list(uf.find(rhs)).size()){
      uf.merge(lhs, rhs, 0, 0);
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
      uf.merge(rhs, lhs, 0, 0);
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

void congruenceClosureAlgorithm(term & terms, funcName & funcNames, int numTerms, UF & uf, signatureTable & sigTable){
  setSingleton pending;
  setPair combine;
  for(term::iterator it = terms.begin(); it != terms.end(); ++it){
    // Only add functional symbols with arity > 0
    if(it->size() > 2){
      // Adding equivalance class, not the name of the function 
      pending.insert(it->getList()->next->data);
    }
  }
  while(!pending.empty()){
    combine.clear();
    for(setSingleton::iterator it = pending.begin(); it != pending.end(); ++it){
      linkedList tempLL = terms[*it];
      // We need to update signatures
      // using the unionfind Data Structure
      if(tempLL.size() == 3){
	// linkedList (fname, id, successor_1)
	tempLL.head->next->next->data = uf.find(tempLL.head->next->next->data);
      }
      if(tempLL.size() == 4){
	// linkedList (fname, id, successor_1, successor_2)
	tempLL.head->next->next->data = uf.find(tempLL.head->next->next->data);
	tempLL.head->next->next->next->data = uf.find(tempLL.head->next->next->next->data);
      }
      
      int tempV = sigTable.query(tempLL);
      if(tempV == -1)
	sigTable.enter(tempLL);
      else
	combine.insert(std::make_pair(*it, tempV));
    }
    pending.clear();
    for(setPair::iterator it = combine.begin(); it != combine.end(); ++it){
      int v = it->first, w = it->second;
      if(uf.find(v) != uf.find(w)){
	circularList listFirst = uf.list(uf.find(v));
	circularList listSecond = uf.list(uf.find(w));

	
	std::cout << "Printing first list " << v << " " << uf.find(v) << "\n";
	listFirst.print();
	std::cout << std::endl;
	std::cout << "Printing second list " << w << " " << uf.find(w) << "\n";
	listSecond.print();
	std::cout << std::endl;
	
	int l1 = listFirst.size(), l2 = listSecond.size();
	if(l1 < l2){
	  if(l1 > 0){
	    node * tempIterator = listFirst.tail->next;
	    do{
	      sigTable.remove(terms[tempIterator->data]);
	      pending.insert(tempIterator->data);
	      uf.addPred(uf.find(w), tempIterator->data);
	      tempIterator = tempIterator->next;
	    } while(tempIterator != listFirst.tail->next);	    
	  }
	  uf.merge(uf.find(w), uf.find(v), l2, l1);
	  std::cout << "After Printing first list " << v << " " << uf.find(v) << "\n";
	  listFirst.print();
	  std::cout << std::endl;
	  std::cout << "After Printing second list " << w << " " << uf.find(w) << "\n";
	  listSecond.print();
	  std::cout << std::endl;
	}
	else{
	  if(l2 > 0){
	    node * tempIterator = listSecond.tail->next;
	    do{
	      sigTable.remove(terms[tempIterator->data]);
	      pending.insert(tempIterator->data);
	      uf.addPred(uf.find(v), tempIterator->data);
	      tempIterator = tempIterator->next;
	    } while(tempIterator != listSecond.tail->next);	    
	  }
	  uf.merge(uf.find(v), uf.find(w), l1, l2);
	  std::cout << "After Printing first list " << v << " " << uf.find(v) << "\n";
	  listFirst.print();
	  std::cout << std::endl;
	  std::cout << "After Printing second list " << w << " " << uf.find(w) << "\n";
	  listSecond.print();
	  std::cout << std::endl;
	}
      }
    }    
  }
}
