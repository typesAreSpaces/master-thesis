#include <iostream>
#include <fstream>
#include <string>
#include <ctime>
#include "unionfind.hpp"
#include "signatureTable.hpp"
#include "congruenceClosure.hpp"
#include "produceRandomEqs.hpp"

void randomTest(){
  // Generation of Input Files
  int numTerms, numEqs;
  std::string name;
  generateInputFile(numTerms, numEqs, name);
  
  // Fast Congruence Closure Algorithm
  term terms;
  funcName funcNames;
  UF uf = initializeUF(numTerms, numEqs, terms, funcNames, name);
  signatureTable sigTable = signatureTable();
  
  std::cout << "Output File:\n";
  std::cout << "Checking Equivalence Classes Initially\n";
  for(int i = 0; i < numTerms; ++i)
    std::cout << i << " " << uf.find(i) << std::endl;
  
  congruenceClosureAlgorithm(terms, funcNames, numTerms, uf, sigTable);

  std::cout << "Checking Equivalence Classes After Congruence Closure\n";
  for(int i = 0; i < numTerms; ++i)
    std::cout << i << " " << uf.find(i) << std::endl;
  
}

void correctnessCheck(){
  // Generation of Input Files
  int numTerms, numEqs;
  std::string name;
  generateInputFile(numTerms, numEqs, name);

  // Fast Congruence Closure Algorithm
  term terms;
  funcName funcNames;
  UF uf = initializeUF(numTerms, numEqs, terms, funcNames, name);
  signatureTable sigTable = signatureTable();
  
  congruenceClosureAlgorithm(terms, funcNames, numTerms, uf, sigTable);

  std::ifstream file ("tests/" + name);
  int temp1, temp2, temp3, temp4, lhs, rhs, check = 1;
  file >> temp1 >> temp4;
  for(int i = 0; i < temp1; ++i){
    file >> temp2;
    file >> temp2;
    while(temp2 > 0){
      file >> temp3;
      --temp2;
    }
  }

  int check3 = 1;
  for(int i = 0; i < (numTerms - 1); ++i){
    for(int j = i + 1; j < numTerms; ++j){
      node * temp1 = terms[i].getList(), * temp2 = terms[j].getList();
      if(terms[i].size() > 2 && temp1->data == temp2->data){
	/*
	std::cout << "Terms in i:\n"; 
	terms[i].print();
	std::cout << "Terms in j:\n"; 
	terms[j].print();
	*/
	temp1 = temp1->next;
	temp2 = temp2->next;
	int check2 = 1, node1 = temp1->data, node2 = temp2->data;
	temp1 = temp1->next;
	temp2 = temp2->next;
	for(; temp1 != nullptr; temp1 = temp1->next){
	  int x = temp1->data, y = temp2->data;
	  if(uf.find(x) != uf.find(y)){
	    check2 = 0;
	    break;
	  }
	  temp2 = temp2->next;
	}
	if(check2 == 1){
	  if(uf.find(node1) != uf.find(node2)){
	    check3 = 0;
	    std::cout << "Problematic vertices: " << node1 << " and  " << node2 << std::endl;
	    terms[i].print();
	    std::cout << std::endl;
	    terms[j].print();
	    std::cout << std::endl;
	  }
	}
      }
    }
  }
  if(check3 == 1)
    std::cout << "Congratulations!" << std::endl;
  else
    std::cout << "There is a problem with the algorithm" << std::endl;
}

void performanceTest(){
  // Generation of Input Files
  int numEqs, repetitions = 2, limit = 10000;
  double average;
  std::string name;

  for(int i = 10; i < limit; ++i){
    average = 0;
    for(int j = 0; j < repetitions; ++j){
      name = "test" + std::to_string(i) + "Performance";
      generateInputFile2(i, numEqs, name);

      // Fast Congruence Closure Algorithm
      term terms;
      funcName funcNames;
      UF uf = initializeUF(i, numEqs, terms, funcNames, name);
      signatureTable sigTable = signatureTable();
      clock_t begin = clock();
      congruenceClosureAlgorithm(terms, funcNames, i, uf, sigTable);
      clock_t end = clock();
      average += double(end - begin) / CLOCKS_PER_SEC;
    }
    std::cout << i << "," << average/repetitions << std::endl;
  }
}

int main(){

  //randomTest();
  correctnessCheck();
  //performanceTest();
  
  return 0;
}
