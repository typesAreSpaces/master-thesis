#include "OctagonParser.h"

OctagonParser::OctagonParser(z3::expr_vector const & assertions) : 
  ctx(assertions.ctx()), z3_variables(ctx),
  id_generator(1), id_table(), bounds(), positions() 
{
  // ----------------------------------------
  // This is just a dummy entry
  z3_variables.push_back(ctx.bool_val(true)); 
  // ----------------------------------------

  for(auto const & assertion : assertions){
    auto const & inequality = assertion.arg(0);
    auto const & bound = assertion.arg(1).get_numeral_int();
    unsigned num_operands = inequality.num_args();

    switch(num_operands){
      case 0:
          // Non-negative variable
          setBoundWith1Var(true, inequality, bound);
          break;
      case 1:
          // Negative variable
          setBoundWith1Var(false, inequality.arg(0), bound);
          break;
      case 2:
       {
          auto const & op_name = inequality.decl().name().str();
          if(op_name == "+"){
            setBoundWith2Vars(true, inequality, bound);
            break;
          }
          else if(op_name == "-"){
            setBoundWith2Vars(false, inequality, bound);
            break;
          }
          else
            throw "Error OctagonParser. The operation is not allowed.";
        }
      default:
        throw "Error OctagonParser. The operation is not allowed.";
    }
  }
  // The current id_generator is the
  // number of variables in the assertions
  bounds.insert(2*(id_generator-1)*(id_generator-1), Bound());

#if DEBUG_OCT_PAR_CONST
  for(auto const & x : id_table)
    std::cout << x.first << " |-> " << x.second << std::endl;
  std::cout << std::endl;
  std::cout << bounds << std::endl;
  std::cout << positions << std::endl;
#endif
}

void OctagonParser::setBoundWith1Var(bool is_positive, z3::expr const & var, 
    BoundValue bound){
  checkExprId(var);
  UtvpiPosition position = Octagon(is_positive ? POS : NEG, id_table[var.hash()], ZERO, 0).getUtviPosition();
  bounds.insert(position, Bound(bound));
  updatePositions(is_positive, var, position);
  return;
}

void OctagonParser::setBoundWith2Vars(bool is_addition, z3::expr const & inequality, 
    BoundValue bound){
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
            UtvpiPosition position = Octagon(
                POS                    , id_table[var_1.hash()], 
                is_addition ? POS : NEG, id_table[var_2.hash()]).getUtviPosition();
            bounds.insert(position, Bound(bound));
            updatePositions(true,        var_1, position);
            updatePositions(is_addition, var_2, position);
            return;
          }
        case 1:
          {
            // Negative variable 2
            checkExprId(var_1);
            checkExprId(var_2.arg(0));
            UtvpiPosition position = Octagon(
                POS                    , id_table[var_1.hash()], 
                is_addition ? NEG : POS, id_table[var_2.arg(0).hash()]).getUtviPosition();
            bounds.insert(position, Bound(bound));
            updatePositions(true,         var_1, position);
            updatePositions(!is_addition, var_2.arg(0), position);
            return;
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
            UtvpiPosition position = Octagon(
                NEG                    , id_table[var_1.arg(0).hash()], 
                is_addition ? POS : NEG, id_table[var_2.hash()]).getUtviPosition();
            bounds.insert(position, Bound(bound));
            updatePositions(false,       var_1.arg(0), position);
            updatePositions(is_addition, var_2, position);
            return;
          }
        case 1:
          {
            // Negative variable 2
            checkExprId(var_1.arg(0));
            checkExprId(var_2.arg(0));
            UtvpiPosition position = Octagon(
                NEG                    , id_table[var_1.arg(0).hash()], 
                is_addition ? NEG : POS, id_table[var_2.arg(0).hash()]).getUtviPosition();
            bounds.insert(position, Bound(bound));
            updatePositions(false,        var_1.arg(0), position);
            updatePositions(!is_addition, var_2.arg(0), position);
            return;
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
    z3_variables.push_back(e);
    id_generator++;
  }
}

void OctagonParser::updatePositions(bool is_positive, z3::expr const & e, UtvpiPosition position){
  VarValue index = id_table[e.hash()];

  if(positions.size() <= index)
    positions.resize(index+1);

  if(!e.is_common()){
    if(is_positive){
      positions.insertPositivePosition(index, position);
      return;
    }
    positions.insertNegativePosition(index, position);
    return;
  }
  return;
}
