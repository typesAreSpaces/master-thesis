#include "HornClauses.h"

HornClauses::HornClauses(){
  
}

HornClauses::~HornClauses(){
  for(std::vector<HornClause*>::iterator it = clauses.begin();
      it != clauses.end(); ++it){
    delete *it;
  }
}
