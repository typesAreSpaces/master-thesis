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
  Term::total_num_vertex = 0; // Important to reset total_num_vertex
  auto first_formula = v.arg(0);
  auto second_formula = v.arg(1);

  // this->root_num denotes the id of the root
  // of the Z3_ast. It also denotes, the number
  // of original elements by construction.
  this->root_num = first_formula.id();
  unsigned num_original_terms = this->root_num;
  terms.resize(2*num_original_terms + 1);
  // This term will encode the False particle
  terms[0] = new Term("incomparable", 0, 0);
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
    terms[term_index] = new Term("_", 0, 0);
  // Adding {x_j | 1 <= j <= n} vertices
  // where n is the number of original vertices
  // -- Their location on terms start from this->root_num + 1 --
  for(unsigned term_index = 1; term_index <= num_original_terms; ++term_index)
    terms[num_original_terms + term_index] = new Term("_x" + std::to_string(term_index), 0, 0);
  
  //Extracting first formula
  extractSymbolsAndTerms(first_formula, symbols_to_elim);
  // Remark: The side effect of the previous function introduces
  // more terms since it adds w_j(v) terms
  equivalence_class = UnionFind(Term::getTotalNumTerm());
  
  //Extracting second formula
  removeSymbols(second_formula, symbols_to_elim);

  identifyCommonSymbols();
}

// Here we take the whole formula
// because the interpolantion problem
// is solved as a
// quantifier elimination problem
Terms::Terms(z3::context & ctx, const z3::expr & v, const UncommonSymbols & symbols_to_elim) :
  ctx(ctx),
  symbols_to_elim(symbols_to_elim)
{
  Term::total_num_vertex = 0; // Important to reset total_num_vertex
  // this->root_num denotes the id of the root
  // of the Z3_ast. It also denotes, the number
  // of original elements by construction.
  
  this->root_num= v.id();
  unsigned num_original_terms = this->root_num;
  terms.resize(2*num_original_terms + 1);
  // This term will encode the False particle
  terms[0] = new Term("incomparable", 0, 0);
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
    terms[term_index] = new Term("_", 0, 0);
  // Adding {x_j | 0 <= j < n} vertices
  // where n is the number of original vertices
  // -- Their location on terms start from this->root_num + 1 --
  for(unsigned term_index = 1; term_index <= num_original_terms; ++term_index)
    terms[num_original_terms + term_index] = new Term("_x" + std::to_string(term_index), 0, 0);
  
  //Extracting the formula
  extractTerms(v);
  
  // Remark: The side effect of the previous function introduces
  // more terms since it adds w_j(v) terms
  equivalence_class = UnionFind(Term::getTotalNumTerm());

  identifyCommonSymbols();
}

Terms::~Terms(){
  for(auto it : terms)
    delete it;
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
void Terms::extractSymbolsAndTerms(const z3::expr & v, UncommonSymbols & symbols){

  const unsigned id = v.id();
  assert(id > 0);

  if(v.is_app())  {
    unsigned num_args = v.num_args();
    auto symbol_name = v.decl().name();
    
    for (unsigned index_arg = 0; index_arg < num_args; index_arg++)
      extractSymbolsAndTerms(v.arg(index_arg), symbols);
    
    switch(symbol_name.kind()){
    case Z3_INT_SYMBOL:
      terms[id]->setName(std::to_string(symbol_name.to_int())); //////////// terms
      symbols.insert(std::to_string(symbol_name.to_int()));
      break;
    case Z3_STRING_SYMBOL:
      terms[id]->setName(symbol_name.str());  //////////// terms
      symbols.insert(symbol_name.str());
      if(terms[id]->getName() == "=")
	equations.push_back(std::make_pair(v.arg(0), v.arg(1)));
      if(terms[id]->getName() == "distinct")
	disequations.push_back(std::make_pair(v.arg(0), v.arg(1)));
      break;
    default:
      unreachable();
    }

    //////////// terms
    switch(num_args){
    case 0:
      terms[id]->setArity(0, 0); 
      terms[id]->define();
      break;
    case 1:
      terms[id]->setArity(1, 1);
      terms[id]->addSuccessor(terms[v.arg(0).id()]);
      terms[id]->addOriginalSuccessor(terms[v.arg(0).id()]);
      terms[id]->define();
      break;
    default:
      assert(num_args >= 2);
      terms[id]->setArity(2, num_args);
	  
      // Position of w_2(v)
      const unsigned first_w_term = terms.size(); 
      // Adding w_j(v) vertices/terms
      for(unsigned index_arg = 2; index_arg <= num_args; ++index_arg)
	terms.push_back(new Term("_" + terms[id]->getName() + "_" + std::to_string(index_arg), 2, 2));

      unsigned num_original_terms = this->root_num;
      // Adding edge (v, v_1)
      terms[id]->addSuccessor(terms[v.arg(0).id()]);
      terms[id]->addOriginalSuccessor(terms[v.arg(0).id()]);
      
      // Adding edge (v, w_2(v))
      terms[id]->addSuccessor(terms[first_w_term]);
      for(unsigned index_arg = 2; index_arg <= num_args; ++index_arg){
	terms[first_w_term + index_arg - 2]->setArity(2, 2);

	// Adding edge w_i(v), v_i
	terms[first_w_term + index_arg - 2]->addSuccessor(terms[v.arg(index_arg - 1).id()]);
	terms[id]->addOriginalSuccessor(terms[v.arg(index_arg - 1).id()]);
	
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
      terms[id]->define();
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
      terms[id]->setArity(0, 0);
      terms[id]->define();
      break;
    case 1:
      terms[id]->setArity(1, 1);
      terms[id]->addSuccessor(terms[v.arg(0).id()]);
      terms[id]->addOriginalSuccessor(terms[v.arg(0).id()]);
      terms[id]->define();
      break;
    default:
      assert(num_args >= 2);
      terms[id]->setArity(2, num_args);
      // Position of w_2(v)
      const unsigned first_w_term = terms.size(); 
      // Adding w_j(v) vertices/terms
      for(unsigned index_arg = 2; index_arg <= num_args; ++index_arg)
	terms.push_back(new Term("_" + terms[id]->getName() + "_" + std::to_string(index_arg), 2, 2));
      unsigned num_original_terms = this->root_num;
      // Adding edge (v, v_1)
      terms[id]->addSuccessor(terms[v.arg(0).id()]);
      terms[id]->addOriginalSuccessor(terms[v.arg(0).id()]);
      
      // Adding edge (v, w_2(v))
      terms[id]->addSuccessor(terms[first_w_term]);
      for(unsigned index_arg = 2; index_arg <= num_args; ++index_arg){
	terms[first_w_term + index_arg - 2]->setArity(2, 2);
	// Adding edge w_i(v), v_i
	terms[first_w_term + index_arg - 2]->addSuccessor(terms[v.arg(index_arg - 1).id()]);
	terms[id]->addOriginalSuccessor(terms[v.arg(index_arg - 1).id()]);
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
      terms[id]->define();
      break;
    }
  }
}

// This method remove symbols that are common
void Terms::removeSymbols(const z3::expr & v, UncommonSymbols & symbols){
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

// Sets common status of common_term
// and collects the position of each
// symbols
void Terms::identifyCommonSymbols(){
  Term * current_term = getReprTerm(root_num), * aux_current_term;
  unsigned arity;
  std::stack<Term*> stack_vertices;
  bool inside_equation = false;
   
  // Traversing the graph (in post-order)
  // to determine if a term is common or not
  // Reference: https://www.geeksforgeeks.org/iterative-postorder-traversal-using-stack/
  do{
    while(current_term != nullptr){
      std::string current_term_name = current_term->getName();
      if(current_term_name == "=")
	inside_equation = true;
      if(current_term_name == "distinct")
	inside_equation = false;
      if(current_term_name == "and")
	inside_equation = false;
      
      arity = current_term->getArity();
      switch(arity){
      case 0:
	stack_vertices.push(current_term);
	current_term = nullptr;
	break;
      case 1:
	stack_vertices.push(current_term);
	current_term = current_term->getLeftChild();
	break;
      case 2:
	stack_vertices.push(current_term->getRightChild()), stack_vertices.push(current_term);
	current_term = current_term->getLeftChild();
	break;
      default:
	throw("Error: Arity cannot be more than 2");
	break;
      }
    }
    current_term = stack_vertices.top();
    stack_vertices.pop();
    arity = current_term->getArity();
    if(arity == 2 && !stack_vertices.empty()
       && current_term->getRightChild()->getId() == stack_vertices.top()->getId()){
      aux_current_term = stack_vertices.top();
      stack_vertices.pop();
      stack_vertices.push(current_term);
      current_term = aux_current_term;
    }
    else{
      // -------------------------------
      // Sets common status of common_term
      // and collects the position of each
      // symbols
      std::string current_term_name = current_term->getName();
      if(inside_equation)
	symbol_locations[current_term_name].push_back(current_term->getId());
      
      bool is_current_term_common = notInSet(current_term_name, symbols_to_elim); 
      for(auto successor : current_term->getSuccessors()){
	if(!is_current_term_common)
	  break;
	is_current_term_common = successor->getSymbolCommonQ();
      }
      current_term->setSymbolCommonQ(is_current_term_common);
      // -------------------------------
      current_term = nullptr;
    }
  } while(!stack_vertices.empty());
}

std::vector<Term*> & Terms::getTerms(){
  return terms;
}

void Terms::setEquivalenceClass(UnionFind & uf){
  equivalence_class = uf;
}

UnionFind & Terms::getEquivalenceClass(){ 
  return equivalence_class;
}

const UnionFind Terms::getDeepEquivalenceClass() const {
  unsigned num_elements = equivalence_class.size();
  std::vector<unsigned> new_elements(num_elements);
  for(unsigned index = 0; index < num_elements; ++index){
    new_elements[index] = equivalence_class[index];
  }
  return UnionFind(new_elements);
}

Term * Terms::getOriginalTerm(unsigned i) const {
  return terms[i];
}

Term * Terms::getReprTerm (unsigned i){
  return terms[equivalence_class.find(i)];
}

Term * Terms::getReprTerm(Term * v){
  return terms[equivalence_class.find(v->getId())];
}

void Terms::merge(Term * u, Term * v){
  if(getReprTerm(u) != getReprTerm(v)){
    getReprTerm(u)->mergePredecessors(getReprTerm(v));
    equivalence_class.merge(u->getId(), v->getId());
  }
}

void Terms::merge(unsigned i, unsigned j){
  auto u = getOriginalTerm(i), v = getOriginalTerm(j);
  if(getReprTerm(u) != getReprTerm(v)){
    getReprTerm(u)->mergePredecessors(getReprTerm(v));
    equivalence_class.merge(u->getId(), v->getId());
  }
}

void Terms::rotate(Term * u, Term * v){
  // Precondition: getReprTerm(u) and getReprTerm(v) should be THE SAME
  // i.e. a rotation only make sense between elements of the same
  // equivalence class
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

z3::context & Terms::getCtx(){
  return ctx;
}

const UncommonSymbols & Terms::getSymbolsToElim(){
  return symbols_to_elim;
}

const std::vector<Equation> & Terms::getEquations(){
  return equations;
}

const std::vector<Disequation> & Terms::getDisequations(){
  return disequations;
}

bool Terms::areEqual(Term * u, Term * v){
  return equivalence_class.find(getReprTerm(u)->getId())
    == equivalence_class.find(getReprTerm(v)->getId());
}

bool Terms::areEqual(unsigned i, unsigned j){
  return equivalence_class.find(getReprTerm(i)->getId())
    == equivalence_class.find(getReprTerm(j)->getId());
}

std::ostream & operator << (std::ostream & os, const Terms & gterms){
  os << "Terms" << std::endl;
  for(auto it : gterms.terms)
    os << *it << std::endl;
  return os;
}
