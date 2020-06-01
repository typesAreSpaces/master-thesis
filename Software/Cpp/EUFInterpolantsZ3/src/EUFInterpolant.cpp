#include "EUFInterpolant.h"

EUFInterpolant::EUFInterpolant(z3::expr_vector const & assertions) : 
  // Congruence Closure step
  Input(assertions), 
  assertions((
        // Unconditional uncommon symbol elimination step
        exposeUncommons()
        , assertions)), 
  // Conditional uncommon symbol elimination step
  hsat(cce, horn_clauses)
{        
  
  for(auto const & equation : assertions){
    hsat.equiv_classes.merge(equation.arg(0), equation.arg(1));
  }
  
#if DEBUG_EXPOSE_UNCOMMS
  std::cout << "After expose uncommons" << std::endl;
  std::cout << horn_clauses << std::endl;
#endif

#if DEBUG_COND_ELIM
  std::cout << "After conditional elimination" << std::endl;
  std::cout << hsat << std::endl;
#endif

#if DEBUG_TEMP
  // DEBUG
  std::cout << subterms << std::endl;
#endif

#if DEBUG_TEMP
  // Testing candidates
  unsigned test_index;
  test_index = 31;
  std::cout << "Replacements for " << subterms[test_index] << std::endl;
  for(auto elem : candidates(subterms[test_index]))
    std::cout << elem << std::endl;
  test_index = 33;
  std::cout << "Replacements for " << subterms[test_index] << std::endl;
  for(auto elem : candidates(subterms[test_index]))
    std::cout << elem << std::endl;
  test_index = 24;
  std::cout << "Replacements for " << subterms[test_index] << std::endl;
  for(auto elem : candidates(subterms[test_index]))
    std::cout << elem << std::endl;
  test_index = 28;
  std::cout << "Replacements for " << subterms[test_index] << std::endl;
  for(auto elem : candidates(subterms[test_index]))
    std::cout << elem << std::endl;

  // Testing allCandidates
  auto test_allCandidates = allCandidates(subterms[34]);
  for(auto const & temp_list : test_allCandidates){
    for(auto const & elem : temp_list)
      std::cout << elem << " ";
    std::cout << std::endl;
  }

  // Testing explainUncommons
  std::cout << subterms[31] << " = " << subterms[24] << std::endl;
  std::cout << explainUncommons(subterms[31], subterms[24]) << std::endl;
  std::cout << subterms[24] << " = " << subterms[31] << std::endl;
  std::cout << explainUncommons(subterms[24], subterms[31]) << std::endl;
  std::cout << subterms[24] << " = " << subterms[24] << std::endl;
  std::cout << explainUncommons(subterms[24], subterms[24]) << std::endl;

  // Testing cartesianProd
  auto t1 = subterms[31]; //31. (c_f c_y1 a_v)
  auto t2 = subterms[21]; //21. c_z1
  auto t3 = subterms[24]; //24. c_s1
  auto t4 = subterms[32]; //32. c_y2
  auto t5 = subterms[34]; //34. (c_f (c_f c_y1 a_v) (c_f c_y2 a_v)) 

  std::cout << "Testing allCandidates" << std::endl;
  std::list<std::list<z3::expr> > abc({{t1, t2}, {t3, t1}, {t4, t1, t2}});
  unsigned temp_index = 1;
  for(auto const & temp : cartesianProd(abc)){
    std::cout << "candidate " << temp_index++ << std::endl;
    std::cout << temp << std::endl;
  }
#endif

  conditionalElimination();

  // buildInterpolant();
  return;
}

EUFInterpolant::~EUFInterpolant(){
#if DEBUG_DESTRUCTOR_EUF
  std::cout << "Bye EUFInterpolant" << std::endl;
#endif
}

z3::expr_vector EUFInterpolant::buildHCBody(z3::expr const & t1, z3::expr const & t2){
  z3::expr_vector hc_body(ctx);
  unsigned num_args = t1.num_args();
  for(unsigned i = 0; i < num_args; i++)
    hc_body.push_back(z3_repr(t1.arg(i)) == z3_repr(t2.arg(i)));
  return hc_body;
}

void EUFInterpolant::exposeUncommons(){
  for(auto iterator : fsym_positions){
    unsigned current_num = iterator.second.size();
    if(current_num >= 2)
      for(unsigned index_1 = 0; index_1 < current_num - 1; index_1++)
        for(unsigned index_2 = index_1 + 1; index_2 < current_num; index_2++){
          z3::expr const & t1 = subterms[iterator.second[index_1]], & t2 = subterms[iterator.second[index_2]];
          // Only expose terms if at least one term is uncommon
          if(!t1.is_common() || !t2.is_common()){
            z3::expr_vector hc_body = buildHCBody(t1, t2);
            z3::expr        hc_head = z3_repr(t1) == z3_repr(t2);
            horn_clauses.add(new HornClause(ctx, hc_body, hc_head, ufe));
          }
        }
  }
  return;
}

void EUFInterpolant::conditionalEliminationEqs(){
  for(auto const & equation : assertions){
    auto const & lhs = equation.arg(0), & rhs = equation.arg(1);

    // KEEP: working here

    if(lhs.is_const()){
      if(rhs.is_const()){
        if(lhs.is_common()){
          if(rhs.is_common()){

          }
          else{

          }
        }
        else{
          if(rhs.is_common()){

          }
          else{

          }
        }
      }
      else{
        if(lhs.is_common()){
          if(rhs.is_common()){

          }
          else{

          }
        }
        else{
          if(rhs.is_common()){

          }
          else{

          }
        }
      }
    }

    else{
      if(rhs.is_const()){
        if(lhs.is_common()){
          if(rhs.is_common()){

          }
          else{

          }
        }
        else{
          if(rhs.is_common()){

          }
          else{

          }
        }
      }
      else{
        if(lhs.is_common()){
          if(rhs.is_common()){

          }
          else{

          }
        }
        else{
          if(rhs.is_common()){

          }
          else{

          }
        }
      }
    }
  }
}

void EUFInterpolant::conditionalEliminationHcs(){
  throw "Not implemented yet!";
}

void EUFInterpolant::conditionalElimination(){
  // Approach: add stuff to the Horn Clauses
  // in the input using add by eliminating
  // uncommon term using the explanation 
  // operator

  // Process original equations
  conditionalEliminationEqs();

  // Process produced Horn clauses
  conditionalEliminationHcs();

  return;
}

std::list<z3::expr> EUFInterpolant::candidates(z3::expr const & e){
  std::list<z3::expr> ans({});

  if(e.is_common()){
    //ans.push_back(e);
    return ans;
  }

  std::set<EqClass> ids({});
  EqClass repr_index = hsat.equiv_classes.find(e.id());
  auto it = hsat.ufe.begin(repr_index);
  auto end = hsat.ufe.end(repr_index);
  for(; it != end; ++it){
    Z3Index index = factory_curry_nodes.getCurryNode(*it)->getZ3Id();
    z3::expr term = subterms[index];
    if(term.is_common() && ids.find(index) == ids.end()){
      ids.insert(index);
      ans.push_back(term);
    }
  }

  return ans;
}

z3::expr_vector EUFInterpolant::explainUncommons(z3::expr const & t1, z3::expr const & t2){
  z3::expr_vector ans(t1.ctx());
  if(t1.id() == t2.id())
    return ans;
  auto partial_explain = hsat.equiv_classes.z3Explain(t1, t2);
  for(auto const & equation : partial_explain){
    if(equation.is_common())
      ans.push_back(equation);
    else
      // --------------------------------
      // Look at the horn_clauses in hsat
      // Identify the proper head term
      // append its antecedent
      // --------------------------------
      for(auto const & hsat_equation 
          : hsat.head_term_indexer[equation.id()]->getAntecedent())
        ans.push_back(hsat_equation);
    
  }
  return ans;
}

std::list<std::list<z3::expr> > EUFInterpolant::allCandidates(z3::expr const & t){
  assert(t.is_app());
  if(t.is_const())
    throw "EUFInterpolant::allCandidates only takes function applications.";

  std::list<std::list<z3::expr> > ans({});
  unsigned num_args = t.num_args();
  for(unsigned index = 0; index < num_args; index++)
    ans.push_back(candidates(t.arg(index)));

  return ans;
}

std::vector<z3::expr_vector> EUFInterpolant::cartesianProd(std::list<std::list<z3::expr> > candidates){
  // ans_size can get really large
  // at most O(n^n)
  // so be aware of 
  // overflow problems
  unsigned ans_size = 1;
  for(auto const & entry : candidates)
    ans_size *= entry.size();

  std::vector<z3::expr_vector> ans;
  ans.reserve(ans_size);
  for(unsigned i = 0; i < ans_size; ++i)
    ans.push_back(z3::expr_vector(ctx));

  if(ans_size){
    unsigned max_repetition = 1;
    for(auto const & entry : candidates){
      unsigned index = 0;
      while(index < ans_size)
        for(auto const & value : entry){
          unsigned index_repetition = 0;
          while(index_repetition++ < max_repetition)
            ans[index++].push_back(value);
        }
      max_repetition *= entry.size();
    }
  }

  return ans;
}

z3::expr EUFInterpolant::buildInterpolant(){
  throw "Not implemented yet!";
}

std::ostream & operator << (std::ostream & os, EUFInterpolant & euf){
  return os;
}
