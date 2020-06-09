#include "OctagonParser.h"

OctagonParser::OctagonParser(z3::expr_vector const & assertions) : 
  ctx(assertions.ctx()), z3_variables(ctx),
  id_generator(1), id_table(), bounds() // FIX: Wrong arity
{
  for(auto const & assertion : assertions){
    auto const & inequality = assertion.arg(0);
    auto const & bound = assertion.arg(1).get_numeral_int();
    unsigned num_operands = inequality.num_args();

    switch(num_operands){
      case 0:
        {
          // Non-negative variable
          UtvpiPosition tmp_position = setBoundWith1Var(true, inequality);
          bounds.insert(tmp_position, Bound(bound));
          break;
        }
      case 1:
        {
          // Negative variable
          UtvpiPosition tmp_position = setBoundWith1Var(false, inequality.arg(0));
          bounds.insert(tmp_position, Bound(bound));
          break;
        }
      case 2:
        {
          auto const & op_name = inequality.decl().name().str();
          if(op_name == "+"){
            UtvpiPosition tmp_position = setBoundWith2Vars(true, inequality);
            bounds.insert(tmp_position, Bound(bound));
            break;
          }
          else if(op_name == "-"){
            UtvpiPosition tmp_position = setBoundWith2Vars(false, inequality);
            bounds.insert(tmp_position, Bound(bound));
            break;
          }
          else
            throw "Error OctagonParser. The operation is not allowed.";
        }
      default:
        throw "Error OctagonParser. The operation is not allowed.";
    }
  }

#if DEBUG_OCT_PAR_CONST
  for(auto const & x : id_table)
    std::cout << x.first << " |-> " << x.second << std::endl;
  std::cout << bounds << std::endl;
#endif
}

UtvpiPosition OctagonParser::setBoundWith1Var(bool is_positive, z3::expr const & var){
  checkExprId(var);
  Octagon tmp(
      is_positive ? POS : NEG, id_table[var.hash()],
      ZERO, 0);
  return tmp.getUtviPosition();
}

UtvpiPosition OctagonParser::setBoundWith2Vars(bool is_addition, z3::expr const & inequality){
  auto const & var_1 = inequality.arg(0);
  auto const & var_2 = inequality.arg(1);

  switch(var_1.num_args()){
    case 0:
      // Non-negative variable 1
      switch(var_2.num_args()){
        case 0:
          {
            // Non-negative variable 2
            checkExprId(var_1);
            checkExprId(var_2);
            Octagon tmp(
                POS                    , id_table[var_1.hash()], 
                is_addition ? POS : NEG, id_table[var_2.hash()]);
            return tmp.getUtviPosition();
          }
        case 1:
          {
            // Negative variable 2
            checkExprId(var_1);
            checkExprId(var_2.arg(0));
            Octagon tmp(
                POS                    , id_table[var_1.hash()], 
                is_addition ? NEG : POS, id_table[var_2.arg(0).hash()]);
            return tmp.getUtviPosition();
          }
        default:
          throw "Not a Utvpi second-variable";
      }
    case 1:
      // Negative variable 1
      switch(var_2.num_args()){
        case 0:
          {
            // Non-negative variable 2
            checkExprId(var_1.arg(0));
            checkExprId(var_2);
            Octagon tmp(
                NEG                    , id_table[var_1.arg(0).hash()], 
                is_addition ? POS : NEG, id_table[var_2.hash()]);
            return tmp.getUtviPosition();
          }
        case 1:
          {
            // Negative variable 2
            checkExprId(var_1.arg(0));
            checkExprId(var_2.arg(0));
            Octagon tmp(
                NEG                    , id_table[var_1.arg(0).hash()], 
                is_addition ? NEG : POS, id_table[var_2.arg(0).hash()]);
            return tmp.getUtviPosition();
          }
        default:
          throw "Not a Utvpi second-variable";
      }
    default:
      throw "Not a Utvpi first-variable";
  }
}

void OctagonParser::checkExprId(z3::expr const & e){
  unsigned e_hash = e.hash();
  if(!inSet(e_hash, id_table)){
    id_table.insert({e_hash, id_generator});
    id_generator++;
  }
}
