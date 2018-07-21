#include "GTerms.h"

void GTerms::visit(Z3_context c, Z3_ast v){
  switch (Z3_get_ast_kind(c, v)) {
  case Z3_NUMERAL_AST: {
    // do something
    //fprintf(out, "%s", Z3_get_numeral_string(c, v));
    break;
  }
  case Z3_APP_AST: {
    unsigned i;
    Z3_app app = Z3_to_app(c, v);
    unsigned num_fields = Z3_get_app_num_args(c, app);
        
    for (i = 0; i < num_fields; i++)
      visit(c, Z3_get_app_arg(c, app, i));

    //--------------------------------------------------
    // do something
    Z3_func_decl d = Z3_get_app_decl(c, app);
    //fprintf(out, "Application of ");
    //visit_symbol(c, Z3_get_decl_name(c, d));
    //fprintf(out, " Id: %d ", Z3_get_ast_id(c, v));
    //fprintf(out, " Hash: %d \n", Z3_get_ast_hash(c, v));
    //fprintf(out, "\n");
    //--------------------------------------------------
	
    break;
  }
  case Z3_QUANTIFIER_AST: {
    // do something
    //fprintf(out, "quantifier");
    break;
  }
  default:
    //fprintf(out, "#unknown");
    break;
  }
}

GTerms::GTerms(Z3_context c, Z3_ast v){
  int numTerms, mark, counter = 0;
  //std::map<unsigned, int> nodeHashes;
  visit(c, v); 
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
