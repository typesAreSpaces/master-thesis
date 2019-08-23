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
Terms::Terms(z3::context & ctx, const z3::expr & v) :
  ctx(ctx)
{
  assert(v.num_args() == 2);
  auto first_formula = v.arg(0);
  auto second_formula = v.arg(1);

  // this->root_num denotes the id of the root
  // of the Z3_ast. It also denotes, the number
  // of original elements by construction.
  this->root_num = first_formula.id();
  unsigned num_original_terms = this->root_num;
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
  extractSymbolsAndTerms(first_formula, symbols_to_elim);
  // Remark: The side effect of the previous function introduces
  // more terms since it adds w_j(v) terms
  equivalence_class = UnionFind(Term::getTotalNumTerm());
  
  //Extracting second formula
  removeSymbols(second_formula, symbols_to_elim);
}

// Here we take the whole formula
// because the interpolantion problem
// is solved as a
// quantifier elimination problem
Terms::Terms(z3::context & ctx, const z3::expr & v, const std::set<std::string> & symbols_to_elim) :
  ctx(ctx),
  symbols_to_elim(symbols_to_elim)
{
  // this->root_num denotes the id of the root
  // of the Z3_ast. It also denotes, the number
  // of original elements by construction.
  this->root_num= v.id();
  unsigned num_original_terms = this->root_num;
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
  extractTerms(v);
  
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
void Terms::extractSymbolsAndTerms(const z3::expr & v, std::set<std::string> & symbols){

  const unsigned id = v.id();
  assert(id > 0);

  if(v.is_app())  {
    unsigned num_args = v.num_args();
    auto symbol_name = v.decl().name();
    
    for (unsigned index_arg = 0; index_arg < num_args; index_arg++)
      extractSymbolsAndTerms(v.arg(index_arg), symbols);
    
    switch(symbol_name.kind()){
    case Z3_INT_SYMBOL:
      terms[id]->setName(std::to_string(symbol_name.to_int()));    
      symbols.insert(std::to_string(symbol_name.to_int()));
      break;
    case Z3_STRING_SYMBOL:
      terms[id]->setName(symbol_name.str());
      symbols.insert(symbol_name.str());
      if(terms[id]->getName() == "=")
		equations.push_back(std::make_pair(v.arg(0), v.arg(1)));
      if(terms[id]->getName() == "distinct")
		disequations.push_back(std::make_pair(v.arg(0), v.arg(1)));
      break;
    default:
      unreachable();
    }

    switch(num_args){
    case 0:
      terms[id]->setArity(0);
	  terms[id]->define();
      break;
    case 1:
      terms[id]->setArity(1);
      terms[id]->addSuccessor(terms[v.arg(0).id()]);
	  terms[id]->define();
      break;
    default:
      assert(num_args >= 2);
      terms[id]->setArity(2);
	  
      // Position of w_2(v)
      const unsigned first_w_term = terms.size(); 
      // Adding w_j(v) vertices/terms
      for(unsigned index_arg = 2; index_arg <= num_args; ++index_arg)
		terms.push_back(new Term("_" + terms[id]->getName() + "_" + std::to_string(index_arg), 2));

      unsigned num_original_terms = this->root_num;
      // Adding edge (v, v_1)
      terms[id]->addSuccessor(terms[v.arg(0).id()]);
      // Adding edge (v, w_2(v))
      terms[id]->addSuccessor(terms[first_w_term]);
	  terms[id]->define();
      for(unsigned index_arg = 2; index_arg <= num_args; ++index_arg){
		terms[first_w_term + index_arg - 2]->setArity(2);
		// Adding edge w_i(v), v_i
		terms[first_w_term + index_arg - 2]->addSuccessor(terms[v.arg(index_arg - 1).id()]);
		if(index_arg == num_args){
		  // Adding edge ( w_{d(v)}(v), x_{d(v)} )
		  terms[first_w_term + index_arg - 2]->addSuccessor(terms[num_original_terms + num_args]);
		}
		else{
		  // Adding edge ( w_i(v), w_{i+1}(v) )
		  terms[first_w_term + index_arg - 2]->addSuccessor(terms[first_w_term + index_arg - 1]);
		}
		terms[first_w_term + index_arg - 2]->define();
      }
      break;
    }
  }
}

// This method extracts terms
void Terms::extractTerms(const z3::expr & v){

  const unsigned id = v.id();
  assert(id > 0);

  if(v.is_app())  {
    unsigned num_args = v.num_args();
    auto symbol_name = v.decl().name();
    
    for (unsigned index_arg = 0; index_arg < num_args; index_arg++)
      extractTerms(v.arg(index_arg));
    
    switch(symbol_name.kind()){
    case Z3_INT_SYMBOL:
      terms[id]->setName(std::to_string(symbol_name.to_int()));    
      break;
    case Z3_STRING_SYMBOL:
      terms[id]->setName(symbol_name.str());
      if(terms[id]->getName() == "=")
		equations.push_back(std::make_pair(v.arg(0), v.arg(1)));
      if(terms[id]->getName() == "distinct")
		disequations.push_back(std::make_pair(v.arg(0), v.arg(1)));
      break;
    default:
      unreachable();
    }

    switch(num_args){
    case 0:
      terms[id]->setArity(0);
	  terms[id]->define();
      break;
    case 1:
      terms[id]->setArity(1);
      terms[id]->addSuccessor(terms[v.arg(0).id()]);
	  terms[id]->define();
      break;
    default:
      assert(num_args >= 2);
      terms[id]->setArity(2);
      // Position of w_2(v)
      const unsigned first_w_term = terms.size(); 
      // Adding w_j(v) vertices/terms
      for(unsigned index_arg = 2; index_arg <= num_args; ++index_arg)
		terms.push_back(new Term("_" + terms[id]->getName() + "_" + std::to_string(index_arg), 2));
      unsigned num_original_terms = this->root_num;
      // Adding edge (v, v_1)
      terms[id]->addSuccessor(terms[v.arg(0).id()]);
      // Adding edge (v, w_2(v))
      terms[id]->addSuccessor(terms[first_w_term]);
	  terms[id]->define();
      for(unsigned index_arg = 2; index_arg <= num_args; ++index_arg){
		terms[first_w_term + index_arg - 2]->setArity(2);
		// Adding edge w_i(v), v_i
		terms[first_w_term + index_arg - 2]->addSuccessor(terms[v.arg(index_arg - 1).id()]);
		if(index_arg == num_args){
		  // Adding edge ( w_{d(v)}(v), x_{d(v)} )
		  terms[first_w_term + index_arg - 2]->addSuccessor(terms[num_original_terms + num_args]);
		}
		else{
		  // Adding edge ( w_i(v), w_{i+1}(v) )
		  terms[first_w_term + index_arg - 2]->addSuccessor(terms[first_w_term + index_arg - 1]);
		}
		terms[first_w_term + index_arg - 2]->define();
      }
      break;
    }
  }
}

// This method remove symbols that are common
void Terms::removeSymbols(const z3::expr & v,
						  std::set<std::string> & symbols){
  if(v.is_app()){
    unsigned num_args = v.num_args();
    auto symbol_name = v.decl().name();
    
    for (unsigned index_arg = 0; index_arg < num_args; ++index_arg)
      removeSymbols(v.arg(index_arg), symbols);
    
    switch (symbol_name.kind()) {
    case Z3_INT_SYMBOL:
      symbols.erase(std::to_string(symbol_name.to_int()));
      break;
    case Z3_STRING_SYMBOL:
      symbols.erase(symbol_name.str());
      break;
    default:
      unreachable();
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

const std::vector<Equation> & Terms::getEquations(){
  return equations;
}

const std::vector<Disequation> & Terms::getDisequations(){
  return disequations;
}

std::ostream & operator << (std::ostream & os, const Terms & gterms){
  os << "Terms" << std::endl;
  for(auto it = gterms.terms.begin(); it != gterms.terms.end(); ++it)
    os << **it << std::endl;
  return os;
}
