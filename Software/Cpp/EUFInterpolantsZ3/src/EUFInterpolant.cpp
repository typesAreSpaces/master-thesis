#include "EUFInterpolant.h"
#include <z3++.h>

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

#if DEBUG_HSAT_INTER
  std::cout << "After conditional elimination" << std::endl;
  std::cout << hsat << std::endl;
#endif

#if DEBUG_TEMP
  std::cout << "All the subterms" << std::endl;
  std::cout << subterms << std::endl;
#endif

#if DEBUG_TEMP
  std::cout << "BEGIN temporal testing" << std::endl;

  auto t1 = subterms[31]; //31. (c_f c_y1 a_v)
  auto t2 = subterms[21]; //21. c_z1
  auto t3 = subterms[24]; //24. c_s1
  auto t4 = subterms[32]; //32. c_y2
  auto t5 = subterms[34]; //34. (c_f (c_f c_y1 a_v) (c_f c_y2 a_v)) 
  auto t6 = subterms[33]; //33. (c_f c_y2 a_v)
  auto t7 = subterms[28]; //28. c_s2
  auto t8 = subterms[22]; //22. a_v

  // Testing candidates
  std::cout << "Testing candidates" << std::endl;
  std::cout << "Candidates for " << t1 << std::endl;
  for(auto elem : candidates(t1))
    std::cout << elem << std::endl;
  std::cout << "Candidates for " << t6 << std::endl;
  for(auto elem : candidates(t6))
    std::cout << elem << std::endl;
  std::cout << "Candidates for " << t3 << std::endl;
  for(auto elem : candidates(t3))
    std::cout << elem << std::endl;
  std::cout << "Candidates for " << t7 << std::endl;
  for(auto elem : candidates(t7))
    std::cout << elem << std::endl;

  // Testing allCandidates
  std::cout << "Testing allCandidates" << std::endl;
  std::cout << "for " << t5 << std::endl;
  for(auto const & temp_list : allCandidates(t5)){
    for(auto const & elem : temp_list)
      std::cout << elem << " ";
    std::cout << std::endl;
  }
  //std::cout << "Testing allCandidates" << std::endl;
  //std::cout << "for " << t8 << std::endl;
  //for(auto const & temp_list : allCandidates(t8)){
  //for(auto const & elem : temp_list)
  //std::cout << elem << " ";
  //std::cout << std::endl;
  //}

  // Testing explainUncommons
  std::cout << "Testing explainUncommons" << std::endl;
  std::cout << t1 << " = " << t3 << std::endl;
  std::cout << explainUncommons(t1, t3) << std::endl;
  std::cout << t3 << " = " << t1 << std::endl;
  std::cout << explainUncommons(t3, t1) << std::endl;
  std::cout << t3 << " = " << t3 << std::endl;
  std::cout << explainUncommons(t3, t3) << std::endl;

  // Testing cartesianProd
  std::cout << "Testing cartesianProd" << std::endl;
  std::list<std::list<z3::expr> > abc({{t1, t2}, {t3, t1}, {t4, t1, t2}});
  unsigned temp_index = 1;
  for(auto const & temp : cartesianProd(abc)){
    std::cout << "candidate " << temp_index++ << std::endl;
    std::cout << temp << std::endl;
  }
  std::list<std::list<z3::expr> > def({{}});
  temp_index = 1;
  for(auto const & temp : cartesianProd(def)){
    std::cout << "candidate " << temp_index++ << std::endl;
    std::cout << temp << std::endl;
  }

  // Testing composition of cartesianProd and allCandidates
  std::cout << "Testing composition of cartesianProd and allCandidates" << std::endl;

  std::cout << "for " << t5 << std::endl;
  for(auto const & w : cartesianProd(allCandidates(t5)))
    std::cout << w << std::endl;

  //std::cout << "for " << t8 << std::endl;
  //for(auto const & w : cartesianProd(allCandidates(t8)))
  //std::cout << w << std::endl;

  std::cout << "END temporal testing" << std::endl;

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
          z3::expr const 
            & t1 = subterms[iterator.second[index_1]], 
            & t2 = subterms[iterator.second[index_2]];
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
#if DEBUG_COND_ELIM_EQS
  std::cout << "conditionalElimination" << std::endl;
#endif

  for(auto const & equation : assertions){
    auto const & lhs = equation.arg(0), & rhs = equation.arg(1);
#if DEBUG_COND_ELIM_EQS
    std::cout << "--Processing this equation: " << equation << std::endl;
#endif

    // FIX: the equivalent class shouldn't be ufe
    // Remember that the z3 terms are not congruent,
    // their constants are!
    // UPDATE: The latter is already addressed.
    // Needs testing however.
    // FIX: add uses ufe.. This must be changed.
    // to the CongruenceClosureExplain
    // FIX: there is a problem. Check the output..

    if(lhs.is_const()){
      if(rhs.is_const()){
#if DEBUG_COND_ELIM_EQS 
        std::cout << "----Case lhs constant rhs constant" << std::endl;
#endif
        for(auto const & e_x : candidates(lhs)){
          for(auto const & e_y : candidates(rhs)){
            Explanation expl(ctx);
            expl.add(explainUncommons(e_x, lhs));
            expl.add(explainUncommons(e_y, rhs));
            horn_clauses.add(new HornClause(ctx, 
                  expl.result, 
                  e_x == e_y));
#if DEBUG_COND_ELIM_EQS
            std::cout << e_x << ", " << e_y << std::endl;
#endif
          }
        }
      }
      else{
#if DEBUG_COND_ELIM_EQS 
        std::cout << "----Case lhs constant rhs function app" << std::endl;
#endif
        for(auto const & e_x : candidates(lhs)){
          for(auto const & e_f_y : candidates(rhs)){
            Explanation expl(ctx);
            expl.add(explainUncommons(e_x, lhs));
            expl.add(explainUncommons(e_f_y, rhs));
            horn_clauses.add(new HornClause(ctx, 
                  expl.result, 
                  e_x == e_f_y));
#if DEBUG_COND_ELIM_EQS
            std::cout << e_x << ", " << e_f_y << std::endl;
#endif
          }
          z3::func_decl f_y = rhs.decl();
          for(auto const & arguments_f_y : cartesianProd(allCandidates(rhs))){
            Explanation expl(ctx);
            expl.add(explainUncommons(e_x, lhs));
            unsigned _index = 0;
            for(auto const & arg_f_y : arguments_f_y)
              expl.add(explainUncommons(rhs.arg(_index++), arg_f_y));
            horn_clauses.add(new HornClause(ctx, 
                  expl.result, 
                  e_x == f_y(arguments_f_y)));
#if DEBUG_COND_ELIM_EQS
            std::cout << e_x << ", " << f_y(arguments_f_y) << std::endl;
#endif
          }
        }
      }
    }
    else{
      if(rhs.is_const()){
#if DEBUG_COND_ELIM_EQS 
        std::cout << "----Case lhs function app rhs constant" << std::endl;
#endif
        for(auto const & e_y : candidates(rhs)){
          for(auto const & e_f_x : candidates(lhs)){
            Explanation expl(ctx);
            expl.add(explainUncommons(e_f_x, lhs));
            expl.add(explainUncommons(e_y, rhs));
#if DEBUG_COND_ELIM_EQS
            std::cout << e_f_x << ", " << e_y << std::endl;
#endif
            horn_clauses.add(new HornClause(ctx, 
                  expl.result, 
                  e_f_x == e_y));
          }
          z3::func_decl f_x = lhs.decl();
          for(auto const & arguments_f_x : cartesianProd(allCandidates(lhs))){
            Explanation expl(ctx);
            unsigned _index = 0;
            for(auto const & arg_f_x : arguments_f_x)
              expl.add(explainUncommons(lhs.arg(_index++), arg_f_x));
            expl.add(explainUncommons(e_y, rhs));
#if DEBUG_COND_ELIM_EQS
            std::cout << f_x(arguments_f_x) << ", " << e_y << std::endl;
#endif
            horn_clauses.add(new HornClause(ctx, 
                  expl.result, 
                  f_x(arguments_f_x) == e_y));
          }
        }
      }
      else{
#if DEBUG_COND_ELIM_EQS 
        std::cout << "----Case lhs function app rhs function app" << std::endl;
#endif
        for(auto const & e_f_x : candidates(lhs)){
          for(auto const & e_f_y : candidates(rhs)){
            Explanation expl(ctx);
            expl.add(explainUncommons(e_f_x, lhs));
            expl.add(explainUncommons(e_f_y, rhs));
#if DEBUG_COND_ELIM_EQS
            std::cout << e_f_x << ", " << e_f_y << std::endl;
#endif
            horn_clauses.add(new HornClause(ctx, 
                  expl.result, 
                  e_f_x == e_f_y));
          }
          z3::func_decl f_y = rhs.decl();
          for(auto const & arguments_f_y : cartesianProd(allCandidates(rhs))){
            Explanation expl(ctx);
            expl.add(explainUncommons(e_f_x, lhs));
            unsigned _index = 0;
            for(auto const & arg_f_y : arguments_f_y)
              expl.add(explainUncommons(rhs.arg(_index++), arg_f_y));
#if DEBUG_COND_ELIM_EQS
            std::cout << e_f_x << ", " << f_y(arguments_f_y) << std::endl;
#endif
            horn_clauses.add(new HornClause(ctx, 
                  expl.result, 
                  e_f_x == f_y(arguments_f_y)));
          }
        }
        z3::func_decl f_x = lhs.decl();
        for(auto const & arguments_f_x : cartesianProd(allCandidates(lhs))){
          for(auto const & e_f_y : candidates(rhs)){
            Explanation expl(ctx);
            unsigned _index = 0;
            for(auto const & arg_f_x : arguments_f_x)
              expl.add(explainUncommons(lhs.arg(_index++), arg_f_x));
            expl.add(explainUncommons(e_f_y, rhs));
#if DEBUG_COND_ELIM_EQS
            std::cout << f_x(arguments_f_x) << ", " << e_f_y << std::endl;
#endif
            horn_clauses.add(new HornClause(ctx, 
                  expl.result, 
                  f_x(arguments_f_x) == e_f_y));
          }
          z3::func_decl f_y = rhs.decl();
          for(auto const & arguments_f_y : cartesianProd(allCandidates(rhs))){
            Explanation expl(ctx);
            unsigned _index = 0;
            for(auto const & arg_f_x : arguments_f_x)
              expl.add(explainUncommons(lhs.arg(_index++), arg_f_x));
            _index = 0;
            for(auto const & arg_f_y : arguments_f_y)
              expl.add(explainUncommons(rhs.arg(_index++), arg_f_y));
#if DEBUG_COND_ELIM_EQS
            std::cout << f_x(arguments_f_x) << ", " << f_y(arguments_f_y) << std::endl;
#endif
            horn_clauses.add(new HornClause(ctx, 
                  expl.result, 
                  f_x(arguments_f_x) == f_y(arguments_f_y)));
          }
        }
      }
    }
  }
}

void EUFInterpolant::conditionalElimination(){
  // Approach: add stuff to the Horn Clauses
  // in the input using add by eliminating
  // uncommon term using the explanation 
  // operator

#if DEBUG_COND_ELIM
  std::cout << horn_clauses << std::endl;
#endif

  // Process original equations
  conditionalEliminationEqs();

  // KEEP: working here
  unsigned _index = 0;
  for(auto const & element : horn_clauses)
    if(element->isCommon())
      std::cout << _index++ << " " << *element << std::endl;

#if DEBUG_COND_ELIM
  std::cout << horn_clauses << std::endl;
#endif

  return;
}

std::list<z3::expr> EUFInterpolant::candidates(z3::expr const & e){
  std::list<z3::expr> ans({});

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
    else{
      // --------------------------------
      // Look at the horn_clauses in hsat
      // Identify the proper head term
      // append its antecedent
      // --------------------------------
      auto const & entry = hsat.head_term_indexer.find(equation.id());
      if(entry == hsat.head_term_indexer.end()){
        // --------------------------------------------------
        // This case couldn't match the equation to any
        // head-term of the Horn clauses. So it just adds 
        // the equation to the explanation because it means
        // that the equation is an assertion from the initial
        // Input
        // --------------------------------------------------
        if(equation.is_common())
          ans.push_back(equation);
      }
      else
        // -------------------------------------------------------
        // This case handles when the equation matches a head-term
        // of a Horn clause and adds to the explanation 
        // the equations in the antecedent of this Horn clause
        // -------------------------------------------------------
        for(auto const & hsat_equation : entry->second->getAntecedent())
          ans.push_back(hsat_equation);
    }

  }
  return ans;
}

std::list<std::list<z3::expr> > EUFInterpolant::allCandidates(z3::expr const & t){
  assert(t.is_app() && !t.is_const());

  std::list<std::list<z3::expr> > ans({});
  // The following test if the function symbol
  // is not common
  auto f = t.decl().name().str();
  if(f[0] != 'c'){
    ans.push_back(std::list<z3::expr>({}));
    return ans;
  }

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
