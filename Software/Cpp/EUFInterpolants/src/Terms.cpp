#include "Terms.h"

// Remark: We take as number of terms the
// max id in the first conjunction of the input
// formula, which is the ID of the root of
// the first conjunction under the hypothesis
// that IDs are given by a PostOrder traversing
// of the graph
// Remark 2: The general format for the SMT2 file is the following:
// <declarations>
// definition of formula A (i.e. first_formula)
// definition of formula B (i.e. second_formula)
// assert [Interp] formula A
// assert formula B
Terms::Terms(Z3_context ctx, Z3_ast v){
  Z3_app app = Z3_to_app(ctx, v);
  assert(Z3_get_app_num_args(ctx, app) == 2);
  auto first_formula = Z3_get_app_arg(ctx, app, 0);
  auto second_formula = Z3_get_app_arg(ctx, app, 1);

  // this->root_num denotes the id of the root
  // of the Z3_ast. It also denotes, the number
  // of original elements by construction.
  this->root_num = Z3_get_ast_id(ctx, first_formula);
  unsigned num_original_terms = this->root_num;
  std::set<std::string> symbols_first_formula, symbols_second_formula;
  terms.resize(2*num_original_terms + 1);
  // This term will encode the False particle
  terms[0] = new Term("incomparable", 0);
  terms[0]->define();
  // --------------------------------------
  // The order of the next two for loops is
  // important due to the side-effect of the
  // new Term() object
  // --------------------------------------
  // Adding placeholders for the
  // actual terms
  // The initial name "_" is important
  // because we can filter non used terms
  // if they start with that character
  for(unsigned term_index = 1; term_index <= num_original_terms; ++term_index)
    terms[term_index] = new Term("_", 0);
  // Adding {x_j | 1 <= j <= n} vertices
  // where n is the number of original vertices
  // -- Their location on terms start from this->root_num + 1 --
  for(unsigned term_index = 1; term_index <= num_original_terms; ++term_index)
    terms[num_original_terms + term_index] = new Term("_x" + std::to_string(term_index), 0);
  
  //Extracting first formula
  extractSymbolsAndTerms(ctx, first_formula, symbols_first_formula);
  // Remark: The side effect of the previous function introduces
  // more terms since it adds w_j(v) terms
  equivalence_class = UnionFind(Term::getTotalNumTerm());
  
  //Extracting second formula
  extractSymbols(ctx, second_formula, symbols_second_formula);
  
  std::set_difference(symbols_first_formula.begin(), symbols_first_formula.end(),
		      symbols_second_formula.begin(), symbols_second_formula.end(),
		      std::inserter(symbols_to_elim, symbols_to_elim.end()));
}

// Here we take the whole formula
// because the interpolantion problem
// is solved as a
// quantifier elimination problem
Terms::Terms(Z3_context ctx, Z3_ast v, const std::set<std::string> & symbols_to_elim) :
  symbols_to_elim(symbols_to_elim){
  // this->root_num denotes the id of the root
  // of the Z3_ast. It also denotes, the number
  // of original elements by construction.
  this->root_num= Z3_get_ast_id(ctx, v);
  unsigned num_original_terms = this->root_num;
  std::set<std::string> symbols_first_formula, symbols_second_formula;
  terms.resize(2*num_original_terms + 1);
  // This term will encode the False particle
  terms[0] = new Term("incomparable", 0);
  terms[0]->define();
  // The order of the next two for loops is
  // important due to the side-effect of the
  // new Term() object
  // --------------------------------------
  // Adding placeholders for the
  // actual terms
  // The initial name "_" is important
  // because we can filter non used terms
  // if they start with that character
  for(unsigned term_index = 1; term_index <= num_original_terms; ++term_index)
    terms[term_index] = new Term("_", 0);
  // Adding {x_j | 0 <= j < n} vertices
  // where n is the number of original vertices
  // -- Their location on terms start from this->root_num + 1 --
  for(unsigned term_index = 1; term_index <= num_original_terms; ++term_index)
    terms[num_original_terms + term_index] = new Term("_x" + std::to_string(term_index), 0);
  
  //Extracting the formula
  extractSymbolsAndTerms(ctx, v, symbols_first_formula);
  
  // Remark: The side effect of the previous function introduces
  // more terms since it adds w_j(v) terms
  equivalence_class = UnionFind(Term::getTotalNumTerm());
}

Terms::~Terms(){
  for(std::vector<Term*>::iterator it = terms.begin();
      it != terms.end(); ++it)
    delete *it;
}

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
void Terms::extractSymbolsAndTerms(Z3_context c, Z3_ast v, std::set<std::string> & symbols){

  const unsigned id = Z3_get_ast_id(c, v);
  assert(id > 0);
	
  switch (Z3_get_ast_kind(c, v)) {
  case Z3_NUMERAL_AST: {
    // do something
    terms[id]->setName(Z3_get_numeral_string(c, v));
    symbols.insert(Z3_get_numeral_string(c, v));
    terms[id]->setArity(0);
    break;
  }
  case Z3_APP_AST: {
    Z3_app app = Z3_to_app(c, v);
    unsigned num_args = Z3_get_app_num_args(c, app);
    
    for (unsigned i = 0; i < num_args; ++i)
      extractSymbolsAndTerms(c, Z3_get_app_arg(c, app, i), symbols);

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
    
    switch(num_args){
    case 0:
      terms[id]->setArity(num_args);
      break;
    case 1:
      terms[id]->setArity(num_args);
      terms[id]->addSuccessor(terms[ Z3_get_ast_id(c, Z3_get_app_arg(c, app, 0)) ]);
      break;
    default:
      assert(num_args >= 2);
      terms[id]->setArity(2);
	  
      // Position of w_2(v)
      const unsigned first_w_term = terms.size(); 
      // Adding w_j(v) vertices/terms
      for(unsigned arg_index = 2; arg_index <= num_args; ++arg_index)
	terms.push_back(new Term("_" + terms[id]->getName() + "_" + std::to_string(arg_index), 2));

      unsigned num_original_terms = this->root_num;
      // Adding edge (v, v_1)
      terms[id]->addSuccessor(terms[Z3_get_ast_id(c, Z3_get_app_arg(c, app, 0))]);
      // Adding edge (v, w_2(v))
      terms[id]->addSuccessor(terms[first_w_term]);
      for(unsigned arg_index = 2; arg_index <= num_args; ++arg_index){
	// std::cout << "Current id: " << id << " Current arg index: " << arg_index - 2 << std::endl;
	// Adding edge w_i(v), v_i
	terms[first_w_term + arg_index - 2]->addSuccessor(terms[ Z3_get_ast_id(c, Z3_get_app_arg(c, app, arg_index - 1)) ]);
	if(arg_index == num_args){
	  // Adding edge ( w_{d(v)}(v), x_{d(v)} )
	  terms[first_w_term + arg_index - 2]->addSuccessor(terms[num_original_terms + num_args]);
	}
	else{
	  // Adding edge ( w_i(v), w_{i+1}(v) )
	  terms[first_w_term + arg_index - 2]->addSuccessor(terms[first_w_term + arg_index - 1]);
	}
      }
      break;
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
}

// This method extracts symbols
void Terms::extractSymbols(Z3_context c, Z3_ast v,
			   std::set<std::string> & symbols){
  switch (Z3_get_ast_kind(c, v)) {
  case Z3_NUMERAL_AST: {
    // do something
    symbols.insert(Z3_get_numeral_string(c, v));
    break;
  }
  case Z3_APP_AST: {
    Z3_app app = Z3_to_app(c, v);
    unsigned num_args = Z3_get_app_num_args(c, app);
    for (unsigned current_arg = 0; current_arg < num_args; ++current_arg)
      extractSymbols(c, Z3_get_app_arg(c, app, current_arg), symbols);
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

std::vector<Term*> & Terms::getTerms(){
  return terms;
}

UnionFind & Terms::getEquivalenceClass(){
  return equivalence_class;
}

Term * Terms::getOriginalTerm(unsigned i){
  return terms[i];
}

Term * Terms::getReprTerm(unsigned i){
  return terms[equivalence_class.find(i)];
}

Term * Terms::getReprTerm(Term * v){
  return terms[equivalence_class.find(v->getId())];
}

void Terms::merge(Term * u, Term * v){
  // Precondition: getReprTerm(u) and getReprTerm(v) should be different
  // Merge the predecessor's list too!
  if(getReprTerm(u) != getReprTerm(v)){
    getReprTerm(u)->mergePredecessors(getReprTerm(v));
    equivalence_class.merge(u->getId(), v->getId());
  }
}

void Terms::rotate(Term * u, Term * v){
  // Precondition: getReprTerm(u) and getReprTerm(v) should be different 
  // Force vertex u to become
  // vertex v's parent
  assert(getReprTerm(u) == getReprTerm(v));
  u->mergePredecessors(getReprTerm(v));
  equivalence_class.link(u->getId(), getReprTerm(v)->getId());
  equivalence_class.reset(u->getId());
}

unsigned Terms::getRootNum(){
  return root_num;
}

const std::set<std::string> & Terms::getSymbolsToElim(){
  return symbols_to_elim;
}

const std::vector<std::pair<Z3_ast, Z3_ast> > & Terms::getEquations(){
  return equations;
}

const std::vector<std::pair<Z3_ast, Z3_ast> > & Terms::getDisequations(){
  return disequations;
}

std::ostream & operator << (std::ostream & os, const Terms & gterms){
  os << "Terms" << std::endl;
  for(auto it = gterms.terms.begin(); it != gterms.terms.end(); ++it)
    os << **it << std::endl;
  return os;
}
