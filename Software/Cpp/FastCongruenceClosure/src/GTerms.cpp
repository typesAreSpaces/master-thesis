#include "GTerms.h"

void GTerms::visit(z3::expr const & e, std::map<unsigned, int> & nodeHashes) {
  if (e.is_app()) {
    unsigned num = e.num_args();
    for (unsigned i = 0; i < num; i++)
      visit(e.arg(i), nodeHashes);

    // -----------------------------------------------------------------------------------------------------------------------
    // do something
    z3::func_decl f = e.decl();
    int _id = Vertex::getTotalNumVertex();
    nodeHashes.insert(std::make_pair(e.hash(), _id));
    terms.push_back(new Vertex());
    terms[_id]->setName(f.name());
    if(num >== 2){
      // Check this 'mark'
      mark = terms.size();
      terms[_id]->setArity(2);
      // Adding w_j(v) vertices
      for(int j = 2; j <= num; ++j){
	Vertex * temp = new Vertex("_c", 2);
	terms.push_back(temp);
      }

      // -------------------------------------------------------------
      // Successors
      for(int j = 2; j < num - 2; ++j){
	terms[mark + j - 2]->addSuccessor(terms[nodeHashes[e.arg(j).has()]]);
	terms[mark + j - 2]->addSuccessor(terms[mark + j - 1]);
      }
      /*
      in >> _successor;
      terms[_id]->addSuccessor(terms[_successor]);
      terms[_id]->addSuccessor(terms[mark]);
      for(int j = 0; j < num - 2; ++j){
	in >> _successor;
	terms[mark + j]->addSuccessor(terms[_successor]);
	terms[mark + j]->addSuccessor(terms[mark + j + 1]);
      }
      in >> _successor;
      terms[mark + num - 2]->addSuccessor(terms[_successor]);
      terms[mark + num - 2]->addSuccessor(terms[numTerms + _arity]);
      */
      // -------------------------------------------------------------
    }
    else{
      terms[_id]->setArity(num);
      for(int j = 0; j < _arity; ++j){
	terms[_id]->addSuccessor(terms[nodeHashes[e.arg(i).hash()]]);
      }
    }
    //std::cout << "Application of " << f.name() << ": " << e << "\nHash: " << e.hash() << " Arity: " << e.num_args() <<"\n";
    // do something
    // -----------------------------------------------------------------------------------------------------------------------
  }
  else if (e.is_quantifier()) {
    //visit(e.body(), nodeHashes, counter);
    // do something
  }
  else {
    assert(e.is_var());
    // do something
  }
}

GTerms::GTerms(z3::expr const & e){
  int numTerms, mark, counter = 0;
  std::map<unsigned, int> nodeHashes;

  visit(e, nodeHashes); 
}


GTerms::GTerms(std::istream & in){
  int numTerms, _arity, _successor, mark;
  std::string _name;
  
  in >> numTerms;
  terms.resize(2*numTerms);

  for(int i = 0; i < numTerms; ++i)
    terms[i] = new Vertex();

  // Adding {x_j | 0 <= j < n} vertices
  // where n is the number of original vertices
  for(int i = 0; i < numTerms; ++i){
    //terms[numTerms + i] = new Vertex("x" + std::to_string(i), 0);
    terms[numTerms + i] = new Vertex("_x" + std::to_string(i), 0);
  }

  for(int i = 0; i < numTerms; ++i){
    in >> _name >> _arity;
    terms[i]->setName(_name);
    if(_arity >= 2){
      mark = terms.size();
      terms[i]->setArity(2);
      // Adding w_j(v) vertices
      for(int j = 2; j <= _arity; ++j){
	//Vertex * temp = new Vertex("w" + std::to_string(j) + std::to_string(terms[i]->getId()), 2);
	//Vertex * temp = new Vertex(terms[i]->getName(), 2);
	Vertex * temp = new Vertex("_c", 2);
	terms.push_back(temp);
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
  EC = UnionFind(Vertex::getTotalNumVertex());
}

GTerms::~GTerms(){
  for(std::vector<Vertex*>::iterator it = terms.begin();
      it != terms.end(); ++it)
    delete *it;
}

Vertex * GTerms::getTerm(int i){
  return terms[i];
}

UnionFind & GTerms::getEC(){
  return EC;
}

Vertex * GTerms::find(Vertex * v){
  return terms[EC.find(v->getId())];
}

void GTerms::merge(Vertex * u, Vertex * v){
  // Merge the predecessor's list too!
  find(u)->mergePredecessors(find(v));
  EC.merge(u->getId(), v->getId());
}

std::ostream & GTerms::print(std::ostream & os){
  for(std::vector<Vertex*>::iterator it = terms.begin(); it != terms.end(); ++it)
    os << **it << std::endl;
  return os;
}
