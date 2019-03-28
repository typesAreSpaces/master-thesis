#include "ConvertReprToZ3.h"

Converter::Converter(z3::context & c, z3::sort & s) :
  ctx(c), sort_A(s) {
}

z3::expr Converter::convert(Vertex * v){
  unsigned arity = v->getArity();
  z3::expr formula(ctx);
  if(arity == 0)
	formula = ctx.constant(v->getName().c_str(), sort_A);
  else{
	z3::expr_vector arguments(ctx);
	z3::sort_vector signature_domain(ctx);
	auto successors = v->getSuccessors();
	for(auto successor : successors){
	  arguments.push_back(convert(successor));
	  signature_domain.push_back(sort_A);
	}
	z3::func_decl f_z3 = z3::function(v->getName().c_str(), signature_domain, sort_A);
	formula = f_z3(arguments);
  }
  return formula;
}

z3::expr Converter::convert(equality & eq){
  return (convert(eq.first) == convert(eq.second));
}

z3::expr Converter::convert(std::vector<equality> & eqs){
  z3::expr formula(ctx);
  int length = eqs.size();
  formula = convert(eqs[0]);
  for(int i = 1; i < length; ++i)
	formula = formula && convert(eqs[i]);
  return formula;
}

z3::expr Converter::convert(HornClause * hc){
  z3::expr formula(ctx);
  auto antecedent = hc->getAntecedent();
  auto consequent = hc->getConsequent();
  formula = implies(convert(antecedent), convert(consequent));
  return formula;
}
