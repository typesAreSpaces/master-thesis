#include "ConvertReprToZ3.h"

// Are all sorts the same?
Converter::Converter(z3::context & c, const z3::sort & s) :
  ctx(c), sort_A(s) {
}

z3::expr Converter::convert(Term * v){
  
  unsigned arity = v->getOriginalArity();
  z3::expr formula(ctx);
  if(arity == 0)
    formula = ctx.constant(v->getName().c_str(), sort_A);
  else{
    z3::expr_vector arguments(ctx);
    z3::sort_vector signature_domain(ctx);
    auto successors = v->getOriginalSuccessors();
    for(auto successor : successors){
      arguments.push_back(convert(successor));
      signature_domain.push_back(sort_A);
    }
    z3::func_decl f_z3 = z3::function(v->getName().c_str(), signature_domain, sort_A);
    formula = f_z3(arguments);
  }
  return formula;
}

z3::expr Converter::convert(const EquationTerm & eq){
  return convert(eq.first) == convert(eq.second);
}

z3::expr Converter::convert(const std::vector<EquationTerm> & eqs){
  z3::expr formula(ctx);
  int length = eqs.size();
  formula = convert(eqs[0]);
  for(int i = 1; i < length; ++i)
    formula = formula && convert(eqs[i]);
  return formula;
}

z3::expr_vector Converter::convert(const std::vector<Equation> & eqs){
  z3::expr_vector answer(ctx);
  for(auto eq : eqs)
    answer.push_back(eq.first == eq.second);
  return answer;
}

z3::expr Converter::convert(HornClause * hc){
  z3::expr formula(ctx);
  auto antecedent = hc->getAntecedent();
  auto consequent = hc->getConsequent();
  formula = implies(convert(antecedent), convert(consequent));
  return formula;
}

z3::expr_vector Converter::convert(const std::vector<HornClause*> & hcs){
  z3::expr_vector answer(ctx);
  for(auto it = hcs.begin(); it != hcs.end(); ++it)
    answer.push_back(convert(*it));
  return answer;
}

z3::expr Converter::makeConjunction(const z3::expr_vector & v){
  unsigned length = v.size();
  if(length == 0)
    return v.ctx().bool_val(true);
  z3::expr formula(ctx);
  formula = v[0];
  for(unsigned i = 1; i < length; ++i)
    formula = formula && v[i];
  return formula;
}

z3::expr Converter::getAntecedent(const z3::expr & hc){
  if(hc.is_implies())
    return hc.arg(0);
  else
    throw "z3::expr is not a horn clause";
}

z3::expr Converter::getConsequent(const z3::expr & hc){
  if(hc.is_implies())
    return hc.arg(1);
  else
    throw "z3::expr is not a horn clause";
}

z3::expr_vector Converter::extraSimplification(const z3::expr_vector & formulas){
  z3::solver solver(formulas.ctx());
  z3::expr_vector answer(formulas.ctx());
  std::set<unsigned> filter;
  bool areEquivalent;
  
  unsigned length = formulas.size();
  for(unsigned i = 0; i < length - 1; ++i)
    for(unsigned j = i + 1; j < length; ++j){
      areEquivalent = false;

      // Heuristic to choose a formula if they are equivalent
      // The idea is that a formula with greater id() pressumably
      // might be more complex, i.e. it might have more terms
      unsigned _i, _j;
      if(formulas[j].id() < formulas[i].id()){
	_i = i, _j = j;
      }
      else{
	_i = j, _j = i;
      }

      solver.push();
      solver.add(not(implies(formulas[_j], formulas[_i])));
      switch (solver.check()) {
      case z3::unsat:   filter.insert(_i); areEquivalent = true; break;
      case z3::sat:     break;
      case z3::unknown: break;
      }
      solver.pop();
	
      solver.push();
      solver.add(not(implies(formulas[_i], formulas[_j])));
      switch (solver.check()) {
      case z3::unsat:
	if(!areEquivalent)
	  filter.insert(_j);
	break;
      case z3::sat:     break;
      case z3::unknown: break;
      }
      solver.pop();     
    }
  
  for(unsigned i = 0; i < length; ++i)
    if(notInSet(i, filter))
      answer.push_back(formulas[i]);
  return answer;
}

z3::expr_vector Converter::removeUncommonTerms(const z3::expr_vector & formulas){
  z3::solver solver(formulas.ctx());
  z3::expr_vector answer(formulas.ctx());
  
  unsigned length = formulas.size();
  for(unsigned i = 0; i < length; ++i){
    // TODO: Continue working here
    // Requires information about the uncommon symbols
    // Remove them from formulas
  }
  return answer;
}

std::set<std::string> Converter::getSymbols(const z3::expr & formula){
  std::set<std::string> symbols;
  auxiliarGetSymbols(formula, symbols);
  return symbols;
}

void Converter::auxiliarGetSymbols(const z3::expr & e, std::set<std::string> & symbols){
  symbols.insert(e.decl().name().str());
  // std::cout << "Formula " << e << std::endl;
  // std::cout << "Name " << e.decl().name().str() << std::endl;
  if (e.is_app()) {
    unsigned num = e.num_args();
    for (unsigned i = 0; i < num; ++i)
      auxiliarGetSymbols(e.arg(i), symbols);
  }
  else if (e.is_quantifier()) {
  }
  else { 
    assert(e.is_var());
  }
}
