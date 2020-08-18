#include "OctagonTerm.h"

OctagonTerm::OctagonTerm(z3::expr const & e, bool is_raw = true) : z3::expr(e)
{
#if _DEBUG_OCT_TERM_
  if(is_raw)
    std::cout << "Original formula " << e << std::endl;
#endif
  if(!is_raw)
    return;
  octagonize();
#if _DEBUG_OCT_TERM_
  std::cout << "Formula after octagonize " << *this << std::endl;
#endif
  onlyLEQ();
#if _DEBUG_OCT_TERM_
  std::cout << "New formula " << *this << std::endl;
#endif
}

z3::expr OctagonTerm::toZ3() const {
  return *this;
}

void OctagonTerm::update(z3::expr const & e){
  *this = OctagonTerm(e, false);
}

void OctagonTerm::octagonize(){
  auto const & op = this->decl();
  z3::expr result = op(this->arg(0) - this->arg(1), 0).simplify();
  // The following case was setting the lhs with the constant
  // and the rhs with the octagon term
  if(result.is_not() 
      && result.arg(0).decl().decl_kind() == Z3_OP_LE 
      && result.arg(0).arg(0).is_numeral())
    result = result.arg(0).arg(1) < result.arg(0).arg(0);
  if(result.is_not()){
    auto const & non_negated_part = result.arg(0);
    auto const & op_ = non_negated_part.decl();
    auto const & lhs = non_negated_part.arg(0);
    auto const & rhs = non_negated_part.arg(1);
    // lhs is a sum 
    switch(lhs.num_args()){
      case 0: // It means lhs is a num
      case 1: // It means lhs is just a single variable
        update(result);
        return;
      case 2: // It means lhs is a sum of two variables
        if(lhs.arg(1).decl().decl_kind() == Z3_OP_MUL){
          if(lhs.arg(0).decl().decl_kind() == Z3_OP_MUL)
            update(not(op_((-lhs.arg(0).arg(1)) - lhs.arg(1).arg(1), rhs)));
          else
            update(not(op_(lhs.arg(0) - lhs.arg(1).arg(1), rhs)));
        }
        else{
          if(lhs.arg(0).decl().decl_kind() == Z3_OP_MUL)
            update(not(op_((-lhs.arg(0).arg(1)) + lhs.arg(1), rhs)));
          else
            update(not(op_(lhs.arg(0) + lhs.arg(1), rhs)));
        }
        return;
      default:
        throw "Not an octagon";
    }
  }
  else{
    auto const & non_negated_part = result;
    auto const & op_ = non_negated_part.decl();
    auto const & lhs = non_negated_part.arg(0);
    auto const & rhs = non_negated_part.arg(1);
    // lhs is a sum 
    switch(lhs.num_args()){
      case 0: // It means lhs is a num
      case 1: // It means lhs is just a single variable
        update(result);
        return;
      case 2: // It means lhs is a sum of two variables
        if(lhs.arg(1).decl().decl_kind() == Z3_OP_MUL){
          if(lhs.arg(0).decl().decl_kind() == Z3_OP_MUL)
            update(op_((-lhs.arg(0).arg(1)) - lhs.arg(1).arg(1), rhs));
          else
            update(op_(lhs.arg(0) - lhs.arg(1).arg(1), rhs));
        }
        else{
          if(lhs.arg(0).decl().decl_kind() == Z3_OP_MUL)
            update(op_((-lhs.arg(0).arg(1)) + lhs.arg(1), rhs));
          else
            update(op_(lhs.arg(0) + lhs.arg(1), rhs));
        }
        return;
      default:
        throw "Not an octagon";
    }
  }
}

z3::expr OctagonTerm::multiplyByNegativeOne(z3::expr const & e){
  auto const & _result = (-e).simplify();
  z3::expr result = _result;
  if(_result.decl().decl_kind() == Z3_OP_MUL 
      && _result.arg(0).get_numeral_int() == -1)
    result = -_result.arg(1);
  // lhs is a sum 
  switch(result.num_args()){
    case 0: // It means result is a num
    case 1: // It means result is just a single variable
      return result;
    case 2: // It means result is a sum of two variables
      if(result.arg(1).decl().decl_kind() == Z3_OP_MUL){
        if(result.arg(0).decl().decl_kind() == Z3_OP_MUL)
          return (-result.arg(0).arg(1)) - result.arg(1).arg(1);
        else
          return result.arg(0) - result.arg(1).arg(1);
      }
      else{
        if(result.arg(0).decl().decl_kind() == Z3_OP_MUL)
          return (-result.arg(0).arg(1)) + result.arg(1);
        else
          return result.arg(0) + result.arg(1);
      }
    default:
      throw "Not an octagon";
  }
}

void OctagonTerm::onlyLEQ(){
  switch(this->decl().decl_kind()){
    case Z3_OP_EQ:
      update(this->arg(0) <= this->arg(1).simplify()
          && multiplyByNegativeOne(this->arg(0)) <= (-this->arg(1)).simplify());
      return;
    case Z3_OP_DISTINCT:
      update(this->arg(0) <= (this->arg(1)- 1).simplify()
          || multiplyByNegativeOne(this->arg(0)) <= (-this->arg(1)- 1).simplify());
      return;
    case Z3_OP_NOT:
      {
        auto const & pos_part = this->arg(0);
        switch(pos_part.decl().decl_kind()){
          case Z3_OP_EQ:
            update(pos_part.arg(0) <= (pos_part.arg(1)- 1).simplify()
                || multiplyByNegativeOne(pos_part.arg(0)) <= (-pos_part.arg(1)- 1).simplify());
            return;
          case Z3_OP_DISTINCT:
            update(pos_part.arg(0) <= pos_part.arg(1) 
                && multiplyByNegativeOne(pos_part.arg(0)) <= (-pos_part.arg(1)).simplify());
            return;
          case Z3_OP_LE:
            update(multiplyByNegativeOne(pos_part.arg(0)) <= (-pos_part.arg(1) - 1).simplify());
            return;
          case Z3_OP_GE:
            update(pos_part.arg(0) <= (pos_part.arg(1) - 1).simplify());
            return;
          case Z3_OP_LT:
            update(multiplyByNegativeOne(pos_part.arg(0)) <= (-pos_part.arg(1)).simplify());
            return;
          case Z3_OP_GT:
            update(pos_part.arg(0) <= pos_part.arg(1));
            return;
          default:
            throw "Not an octagon";
        }
        return;
      }
    case Z3_OP_LE:
      return;
    case Z3_OP_GE:
      update(multiplyByNegativeOne(this->arg(0)) <= (-this->arg(1)).simplify());
      return;
    case Z3_OP_LT:
      update(this->arg(0) <= (this->arg(1) - 1).simplify());
      return;
    case Z3_OP_GT:
      update(multiplyByNegativeOne(this->arg(0)) <= (-this->arg(1) - 1).simplify());
      return;
    default:
      throw "Not an octagon";
  }
}

