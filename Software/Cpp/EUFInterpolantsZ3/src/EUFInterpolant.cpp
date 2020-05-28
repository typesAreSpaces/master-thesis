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
#if DEBUG_EXPOSE_UNCOMMS
  std::cout << "After expose uncommons" << std::endl;
  std::cout << horn_clauses << std::endl;
#endif

#if DEBUG_COND_ELIM
  std::cout << "After conditional elimination" << std::endl;
  std::cout << hsat << std::endl;
#endif

  //std::cout << hsat.ufe << std::endl;
  //std::cout << factory_curry_nodes << std::endl;
  //unsigned i = 0;
  //for(auto elem : subterms)
    //std::cout 
      //<< ++i << ". Id: " << elem.id() << " " 
      //<< elem << std::endl;

  //unsigned test_index;
  //test_index = 31;
  //std::cout << "Replacements for " << subterms[test_index] << std::endl;
  //std::cout << commonReplacements(subterms[test_index]) << std::endl << std::endl;
  //test_index = 33;
  //std::cout << "Replacements for " << subterms[test_index] << std::endl;
  //std::cout << commonReplacements(subterms[test_index]) << std::endl << std::endl;
  //test_index = 24;
  //std::cout << "Replacements for " << subterms[test_index] << std::endl;
  //std::cout << commonReplacements(subterms[test_index]) << std::endl << std::endl;
  //test_index = 28;
  //std::cout << "Replacements for " << subterms[test_index] << std::endl;
  //std::cout << commonReplacements(subterms[test_index]) << std::endl << std::endl;

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

void EUFInterpolant::conditionalElimination(){
  // Approach: add stuff to the Horn Clauses
  // in the input using add by eliminating
  // uncommon term using the explanation 
  // operator

  // Process original equations
  for(auto const & equation : assertions){
    std::cout << equation << std::endl;
    auto const & lhs = equation.arg(0), & rhs = equation.arg(1);

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





  // Process produced Horn clauses



  return;
}

z3::expr_vector EUFInterpolant::commonReplacements(z3::expr const & e){
  z3::expr_vector ans(e.ctx());

  if(e.is_common()){
    ans.push_back(e);
    return ans;
  }

  std::set<EqClass> ids({});
  EqClass repr_index = hsat.equiv_classes.find(e.id());
  auto it = hsat.ufe.begin(repr_index);
  auto end = hsat.ufe.end(repr_index);
  for(; it != end; ++it){
    Z3Index index = factory_curry_nodes.getCurryNode(*it)->getZ3Id();
    if(subterms[index].is_common() && ids.find(index) == ids.end()){
      ids.insert(index);
      ans.push_back(subterms[index]);
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
