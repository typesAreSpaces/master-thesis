#include <iostream>
#include <fstream>
//#include "GTerms.h"
//#include "unionfind.h"
#include "signatureTable.h"

int main(int argc, char ** argv){
  
  /*
  CircularList<char> * l = new CircularList<char>;
  l->add('a'), l->add('b'), l->add('c');
  CircularList<char> * l2 = new CircularList<char>;
  l2->add('d'), l2->add('e'), l2->add('f');
  l->mergeCircularList(l2);
  l2->add('a');

  l->print(std::cout), l2->print(std::cout);

  delete l, delete l2;

  CircularList<int> l3 = CircularList<int>();
  */
  
  /*
  Vertex
    v1 = Vertex("x", 0),
    v2 = Vertex("f", 1),
    v3 = Vertex("f", 1);
  
  v2.addSuccessor(&v1);
  v3.addSuccessor(&v2);
 
  std::cout << v1 << std::endl;
  std::cout << v2 << std::endl;
  std::cout << v3 << std::endl;

  Vertex
    u1 = Vertex("y", 0),
    u2 = Vertex("g", 2),
    u3 = Vertex("g", 2);
  u2.addSuccessor(&u1), u2.addSuccessor(&u1);
  u3.addSuccessor(&u1), u3.addSuccessor(&u2);

  std::cout << u1 << std::endl;
  std::cout << u2 << std::endl;
  std::cout << u3 << std::endl;

  Vertex u4 = Vertex("h", 3);
  u4.addSuccessor(&v1), u4.addSuccessor(&v3), u4.addSuccessor(&u3);

  std::cout << u4 << std::endl;
  */
  /*
  std::ifstream file;
  file.open(argv[1], std::ifstream::in);
  
  GTerms terms = GTerms(file);
  file.close();
  
  terms.print(std::cout);
  */
  /*
  UnionFind uf = UnionFind(5);
  uf.merge(1, 2), uf.merge(3, 2);
  uf.print(std::cout);
  std::cout << (uf.find(2) == uf.find(3)) << std::endl;
  uf.print(std::cout);
  */

  SignatureTable sigTable = SignatureTable();
  
  return 0;
}
