#include "GTerms.h"

/**
   \brief exit gracefully in case of error.
*/
void GTerms::exitf(const char* message){
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
   \brief exit if unreachable code was reached.
*/
void GTerms::unreachable(){
  exitf("unreachable code was reached");
}

void GTerms::visit(Z3_context c, Z3_ast v, unsigned numTerms, unsigned & counterExtraTerms){
  unsigned id = Z3_get_ast_id(c, v);
  switch (Z3_get_ast_kind(c, v)) {
  case Z3_NUMERAL_AST: {
    // do something
    terms[id]->setName(Z3_get_numeral_string(c, v));
    terms[id]->setArity(0);
    break;
  }
  case Z3_APP_AST: {
    unsigned i, _successor;
    Z3_app app = Z3_to_app(c, v);
    unsigned num_args = Z3_get_app_num_args(c, app);
    for (i = 0; i < num_args; ++i)
      visit(c, Z3_get_app_arg(c, app, i), numTerms, counterExtraTerms);
    //----------------------------------------------------------------------------------------
    // do something
    Z3_func_decl d = Z3_get_app_decl(c, app);
    Z3_symbol s = Z3_get_decl_name(c, d);
    switch (Z3_get_symbol_kind(c, s)) {
    case Z3_INT_SYMBOL:
      terms[id]->setName(std::to_string(Z3_get_symbol_int(c, s)));
      break;
    case Z3_STRING_SYMBOL:
      terms[id]->setName(Z3_get_symbol_string(c, s));
      break;
    default:
      unreachable();
    }
    if(num_args >= 2){
      unsigned mark = terms.size();
      terms[id]->setArity(2);
      // Adding w_j(v) vertices
      for(unsigned j = 2; j <= num_args; ++j){
	Vertex * temp = new Vertex("_c", 2);
	terms.push_back(temp);
	++counterExtraTerms;
      }
      _successor = Z3_get_ast_id(c, Z3_get_app_arg(c, app, 0));
      terms[id]->addSuccessor(terms[_successor]);
      terms[id]->addSuccessor(terms[mark]);
      for(unsigned j = 0; j < num_args - 2; ++j){
	_successor = Z3_get_ast_id(c, Z3_get_app_arg(c, app, j));
	terms[mark + j]->addSuccessor(terms[_successor]);
	terms[mark + j]->addSuccessor(terms[mark + j + 1]);
      }
      _successor = Z3_get_ast_id(c, Z3_get_app_arg(c, app, num_args - 1));
      terms[mark + num_args - 2]->addSuccessor(terms[_successor]);
      terms[mark + num_args - 2]->addSuccessor(terms[numTerms + num_args]);
    }
    else{
      terms[id]->setArity(num_args);
      for(unsigned j = 0; j < num_args; ++j){
	_successor = Z3_get_ast_id(c, Z3_get_app_arg(c, app, j));
	terms[id]->addSuccessor(terms[_successor]);
      }
    }
    //----------------------------------------------------------------------------------------
    break;
  }
  case Z3_QUANTIFIER_AST: {
    //fprintf(out, "quantifier");
    break;
  }
  default:{
    //fprintf(out, "#unknown");
    break;
  }
  }
}

GTerms::GTerms(Z3_context ctx, Z3_ast v){
  unsigned counterExtraTerms = 0, & refCounterExtraTerms = counterExtraTerms;
  Z3_goal g = Z3_mk_goal(ctx, true, false, false);
  Z3_goal_assert(ctx, g, v);
  unsigned numTerms = Z3_goal_num_exprs(ctx, g), mark, counter = 0;
  terms.resize(2*numTerms);
  // Adding {x_j | 0 <= j < n} vertices
  // where n is the number of original vertices
  for(int i = 0; i < numTerms; ++i){
    terms[i] = new Vertex();
    terms[numTerms + i] = new Vertex("_x" + std::to_string(i), 0);
  }
  visit(ctx, v, numTerms, refCounterExtraTerms);
  // ? I'm not sure about the next line
  // UPDATE: Ok, now it's better. Nonetheless, this
  // method needs to be tested
  EC = UnionFind(numTerms + counterExtraTerms);
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
