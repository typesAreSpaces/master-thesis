#include "Terms.h"
#define debugVisit  false
#define debugVisit2 false

/**
   \brief exit gracefully in case of error.
*/
void Terms::exitf(const char* message){
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
   \brief exit if unreachable code was reached.
*/
void Terms::unreachable(){
  exitf("unreachable code was reached");
}

// This method extracts terms and symbols
void Terms::traverse(Z3_context c, Z3_ast v,
					 unsigned numTerms, unsigned & counterExtraTerms,
					 std::set<std::string> & symbols){

  unsigned id = Z3_get_ast_id(c, v);
  if(debugVisit2)
    std::cout << "Just checking the id " << " ID: " << id << std::endl;
	
  switch (Z3_get_ast_kind(c, v)) {
  case Z3_NUMERAL_AST: {
    // do something
    terms[id]->setName(Z3_get_numeral_string(c, v));
    symbols.insert(Z3_get_numeral_string(c, v));
    terms[id]->setArity(0);
    if(debugVisit){
      std::cout << "Application of " << terms[id]->getName()
				<< " ID: " << id << std::endl;
    }
    break;
  }
  case Z3_APP_AST: {
    Z3_app app = Z3_to_app(c, v);
    unsigned i, _successor, mark, num_args = Z3_get_app_num_args(c, app);
    
    for (i = 0; i < num_args; ++i)
      traverse(c, Z3_get_app_arg(c, app, i), numTerms, counterExtraTerms, symbols);

    //-----------------------------------------------------------------------
    // do something
    Z3_func_decl d = Z3_get_app_decl(c, app);
    Z3_symbol s = Z3_get_decl_name(c, d);
    switch (Z3_get_symbol_kind(c, s)) {
    case Z3_INT_SYMBOL:
      terms[id]->setName(std::to_string(Z3_get_symbol_int(c, s)));
      symbols.insert(std::to_string(Z3_get_symbol_int(c, s)));
      break;
    case Z3_STRING_SYMBOL:
      terms[id]->setName(Z3_get_symbol_string(c, s));
      symbols.insert(Z3_get_symbol_string(c, s));
	  if(terms[id]->getName() == "=")
		equations.push_back(std::make_pair(Z3_get_app_arg(c, app, 0),
										   Z3_get_app_arg(c, app, 1)));
      if(terms[id]->getName() == "distinct")
		disequations.push_back(std::make_pair(Z3_get_app_arg(c, app, 0),
											  Z3_get_app_arg(c, app, 1)));
		
      break;
    default:
      unreachable();
    }
    if(num_args > 2){
      mark = terms.size();
      terms[id]->setArity(2);
      // Adding w_j(v) vertices
      for(unsigned j = 2; j <= num_args; ++j){
		terms.push_back(new Vertex("_" + terms[i]->getName()
								   + "_" + std::to_string(j), 2));
		++counterExtraTerms;
      }
      _successor = Z3_get_ast_id(c, Z3_get_app_arg(c, app, 0));
      terms[id]->addSuccessor(terms[_successor]);
      terms[id]->addSuccessor(terms[mark]);
      for(unsigned j = 0; j < num_args - 2; ++j){
		_successor = Z3_get_ast_id(c, Z3_get_app_arg(c, app, j + 1));
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
    //---------------------------------------------------------------------------------
    if(debugVisit){
      std::cout << "Application of " << terms[id]->getName()
				<< " ID: " << id << std::endl;
    }
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
  terms[id]->define();
  if(debugVisit2){
    std::cout << "Just checking the final vertex " << *terms[id] << std::endl;
  }
}

// This method extracts symbols
void Terms::traverse(Z3_context c, Z3_ast v,
					 std::set<std::string> & symbols){
  switch (Z3_get_ast_kind(c, v)) {
  case Z3_NUMERAL_AST: {
    // do something
    symbols.insert(Z3_get_numeral_string(c, v));
    break;
  }
  case Z3_APP_AST: {
    Z3_app app = Z3_to_app(c, v);
    unsigned i, num_args = Z3_get_app_num_args(c, app);
    for (i = 0; i < num_args; ++i)
      traverse(c, Z3_get_app_arg(c, app, i), symbols);
    //---------------------------------------------------------------------------
    // do something
    Z3_func_decl d = Z3_get_app_decl(c, app);
    Z3_symbol s = Z3_get_decl_name(c, d);
    switch (Z3_get_symbol_kind(c, s)) {
    case Z3_INT_SYMBOL:
      symbols.insert(std::to_string(Z3_get_symbol_int(c, s)));
      break;
    case Z3_STRING_SYMBOL:
      symbols.insert(Z3_get_symbol_string(c, s));
      break;
    default:
      unreachable();
    }
    //----------------------------------------------------------------------------
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

Terms::Terms(Z3_context ctx, Z3_ast v){
  Z3_app app = Z3_to_app(ctx, v);
  // Update: let's take as number of terms the
  // max id in the first conjunction of the input
  // formula, which is the ID of the root of
  // the first conjunction under the hypothesis
  // that IDs are given by a PostOrder traversing
  // of the graph
  // Update 2: The general format for the SMT2 file is the following:
  // <declarations>
  // definition of formula A
  // definition of formula B
  // assert [Interp] formula A
  // assert formula B
  unsigned numTerms = Z3_get_ast_id(ctx, Z3_get_app_arg(ctx, app, 0)),
    counterExtraTerms = 0, & refCounterExtraTerms = counterExtraTerms;
  this->root_num = numTerms;
  
  std::set<std::string> symbolsA, symbolsB;
  terms.resize(2*numTerms);

  // The order of the next two for loops is
  // important due to the side-effect of the
  // new Vertex() object
	
  // Adding placeholders for the
  // actual terms
  for(unsigned i = 0; i < numTerms; ++i)
    terms[i] = new Vertex("_", 0);
  // Adding {x_j | 0 <= j < n} vertices
  // where n is the number of original vertices
  for(unsigned i = 0; i < numTerms; ++i)
    terms[numTerms + i] = new Vertex("_x" + std::to_string(i), 0);
  
  //Extracting first formula
  traverse(ctx, Z3_get_app_arg(ctx, app, 0), numTerms, refCounterExtraTerms, symbolsA);
  //Extracting second formula
  traverse(ctx, Z3_get_app_arg(ctx, app, 1), symbolsB);
  
  std::set_difference(symbolsA.begin(), symbolsA.end(),
					  symbolsB.begin(), symbolsB.end(),
					  std::inserter(symbols_to_elim, symbols_to_elim.end()));

  // This symbol will be used to encode the False particle
  terms.push_back(new Vertex("incomparable", 0));
  terms[Vertex::getTotalNumVertex() - 1]->define();

  equivalence_class = UnionFind(Vertex::getTotalNumVertex());
}

Terms::Terms(Z3_context ctx, Z3_ast v, std::set<std::string> & symbols_to_elim) :
  symbols_to_elim(symbols_to_elim){
  unsigned numTerms = Z3_get_ast_id(ctx, v),
    counterExtraTerms = 0,
    & refCounterExtraTerms = counterExtraTerms;
  this->root_num = numTerms;
  std::set<std::string> symbolsA, symbolsB;
  terms.resize(2*numTerms);

  // The order of the next two for loops is
  // important due to the side-effect of the
  // new Vertex() object
	
  // Adding placeholders for the
  // actual terms
  for(unsigned i = 0; i < numTerms; ++i)
    terms[i] = new Vertex("_", 0);
  // Adding {x_j | 0 <= j < n} vertices
  // where n is the number of original vertices
  for(unsigned i = 0; i < numTerms; ++i)
    terms[numTerms + i] = new Vertex("_x" + std::to_string(i), 0);
  
  //Extracting the formula
  traverse(ctx, v, numTerms, refCounterExtraTerms, symbolsA);

  // This symbol will be used to encode the False particle
  terms.push_back(new Vertex("incomparable", 0));
  terms[Vertex::getTotalNumVertex() - 1]->define();

  equivalence_class = UnionFind(Vertex::getTotalNumVertex());
}


Terms::Terms(std::istream & in){
  unsigned numTerms, _arity, _successor, mark;
  std::string _name;
  
  in >> numTerms;
  terms.resize(2*numTerms);

  // Adding placeholders for the
  // actual terms
  for(unsigned i = 0; i < numTerms; ++i)
    terms[i] = new Vertex("_", 0);

  // Adding {x_j | 0 <= j < n} vertices
  // where n is the number of original vertices
  for(unsigned i = 0; i < numTerms; ++i)
    terms[numTerms + i] = new Vertex("_x" + std::to_string(i), 0);

  for(unsigned i = 0; i < numTerms; ++i){
    in >> _name >> _arity;
    terms[i]->setName(_name);
    if(_arity > 2){
      mark = terms.size();
      terms[i]->setArity(2);

	  // Adding w_j(v) vertices
      for(unsigned j = 2; j <= _arity; ++j)
		terms.push_back(new Vertex("_" + terms[i]->getName() +
								   "_" + std::to_string(j), 2));
			
      in >> _successor;
      terms[i]->addSuccessor(terms[_successor]);
      terms[i]->addSuccessor(terms[mark]);
      for(unsigned j = 0; j < _arity - 2; ++j){
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
      for(unsigned j = 0; j < _arity; ++j){
		in >> _successor;       
		terms[i]->addSuccessor(terms[_successor]);
      }
    }
  }

  // This symbol will be used to encode the False particle
  terms.push_back(new Vertex("incomparable", 0));
  terms[Vertex::getTotalNumVertex() - 1]->define();
	
  equivalence_class = UnionFind(Vertex::getTotalNumVertex());
}

Terms::~Terms(){
  for(std::vector<Vertex*>::iterator it = terms.begin();
      it != terms.end(); ++it)
    delete *it;
}

std::vector<Vertex*> & Terms::getTerms(){
  return terms;
}

UnionFind & Terms::getEquivalenceClass(){
  return equivalence_class;
}

Vertex * Terms::getOriginalVertex(unsigned i){
  return terms[i];
}

Vertex * Terms::getVertex(unsigned i){
  return terms[equivalence_class.find(i)];
}

Vertex * Terms::getVertex(Vertex * v){
  return terms[equivalence_class.find(v->getId())];
}

void Terms::merge(Vertex * u, Vertex * v){
  // Precondition, getVertex(u) and getVertex(v) should be different
  // Merge the predecessor's list too!
  if(getVertex(u) != getVertex(v)){
    getVertex(u)->mergePredecessors(getVertex(v));
    equivalence_class.merge(u->getId(), v->getId());
  }
}

void Terms::rotate(Vertex * u, Vertex * v){
  // Force vertex u to become
  // vertex v's parent  
  u->mergePredecessors(getVertex(v));
  equivalence_class.link(u->getId(), getVertex(v)->getId());
  equivalence_class.reset(u->getId());
}

unsigned Terms::getRootNum(){
  return root_num;
}

std::set<std::string> & Terms::getSymbolsToElim(){
  return symbols_to_elim;
}

std::vector<std::pair<Z3_ast, Z3_ast> > & Terms::getEquations(){
  return equations;
}

std::vector<std::pair<Z3_ast, Z3_ast> > & Terms::getDisequations(){
  return disequations;
}

std::ostream & operator << (std::ostream & os, Terms & gterms){
  os << "Terms" << std::endl;
  for(std::vector<Vertex*>::iterator it = gterms.terms.begin();
	  it != gterms.terms.end(); ++it)
    os << **it << std::endl;
  return os;
}
