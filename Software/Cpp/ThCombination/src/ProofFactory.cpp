#include "ProofFactory.h"

ClauseProof::ClauseProof(unsigned id) : 
  id(id), literals({}), clause_subproofs({})
{
}

void ClauseProof::addLiteral(int lit){
  literals.push_back(lit);
}

void ClauseProof::addSubproof(ClauseProof const * subproof){
  clause_subproofs.push_back(subproof);
}

void ClauseProof::updateLiterals(ClauseProof const & clause_proof){
  literals = clause_proof.literals;
}

void ClauseProof::updateResolution(int pivot_id, ClauseProof const & rhs_clause){
  // The following loop removes the pivot in the left-cumulative 
  // list of literals
  for(auto it=literals.begin(); it!=literals.end();){
    if((*it < 0 ? -*it : *it) == pivot_id)
      it = literals.erase(it);
    else
      ++it;
  }
  // The following loop only adds elements from clause_proofs[aux_clause_id].literals
  // when they are not equal to the pivot
  for(auto const & lit : rhs_clause.literals)
    if((lit < 0 ? -lit : lit) != pivot_id) addLiteral(lit);
  literals.sort();
  literals.unique();
}

std::ostream & operator << (std::ostream & os, ClauseProof const & cp){
  os << "clause id: " << cp.id;
  os << " literals: ";
  for(auto const & lit : cp.literals)
    os << lit << " ";
  return os;
}

LitProof::LitProof(unsigned id) : 
  id(id), lit_subproofs({}), clause_subproof(nullptr)
{
}

unsigned LitProof::getId() const {
  return id;
}

void LitProof::addSubproof(LitProof const * lit_proof){
  lit_subproofs.push_back(lit_proof);
}

void LitProof::updateClauseProof(ClauseProof const * clause_proof){
  clause_subproof = clause_proof;
}

ConflictProof::ConflictProof()
{
}

ProofFactory::ProofFactory():
  clause_proofs(), lit_proofs(), conflict_proof()
{
  std::string current_dir = exec("pwd");

  // Setup initial clauses
  std::ifstream cnf_file("/home/jose/booleforce_examples/hole6.cnf", std::fstream::in);
  //std::ifstream cnf_file(current_dir + "/file.cnf", std::fstream::in);
  std::string line;
  std::getline(cnf_file, line);
  unsigned clause_id = 0;
  while(std::getline(cnf_file, line)){
    std::istringstream cnf_file_line(line);
    clause_proofs.emplace_back(clause_id);
    int lit;
    while(true){
      cnf_file_line >> lit;
      if(lit == 0)
        break;
      clause_proofs[clause_id].addLiteral(lit);
    }
    clause_id++;
  }

  system("zchaff ~/booleforce_examples/hole6.cnf > /dev/null");
  //system(("zchaff " + current_dir + "/file.cnf > /dev/null").c_str());
  //system(("rm " + current_dir + "/file.cnf").c_str());

  std::ifstream resolve_trace_file(current_dir + "/resolve_trace", std::fstream::in);
  std::string proof_kind, aux_symbol;

  while(std::getline(resolve_trace_file, line)){
    std::istringstream resolve_trace_line(line);
    resolve_trace_line >> proof_kind;

    if(proof_kind == "CL:"){
      // -------------------------------
      unsigned clause_id, sub_clause_id;
      int pivot_id;
      // -------------------------------
      
      resolve_trace_line >> clause_id;
      resolve_trace_line >> aux_symbol;
      resolve_trace_line >> pivot_id; 
      resolve_trace_line >> sub_clause_id;

      clause_proofs.emplace_back(clause_id);
      auto & lhs_clause = clause_proofs[clause_id];
      lhs_clause.addSubproof(&clause_proofs[sub_clause_id]);
      lhs_clause.updateLiterals(clause_proofs[sub_clause_id]);
      do {
        resolve_trace_line >> pivot_id; 
        resolve_trace_line >> sub_clause_id;
        lhs_clause.addSubproof(&clause_proofs[sub_clause_id]);
        lhs_clause.updateResolution(pivot_id, clause_proofs[sub_clause_id]);
      } while(resolve_trace_line.good());
    }
    else if(proof_kind == "VAR:"){

      // ------------------------------------------------
      unsigned pure_literal, aux_number, polarity, 
               antecedent_clause, lit_repr, sub_lit_repr;
      // ------------------------------------------------

      resolve_trace_line >> pure_literal;
      resolve_trace_line >> aux_symbol;
      resolve_trace_line >> aux_number;
      resolve_trace_line >> aux_symbol;
      resolve_trace_line >> polarity;
      resolve_trace_line >> aux_symbol;
      resolve_trace_line >> antecedent_clause;
      resolve_trace_line >> aux_symbol;

      lit_repr = polarity ? 2*pure_literal : 2*pure_literal + 1;
      lit_proofs.if_enough_push_back_otherwise_resize(lit_repr);
      auto & current_lit = lit_proofs[lit_repr];
      current_lit.updateClauseProof(&clause_proofs[antecedent_clause]);
      while(resolve_trace_line.good()){
        resolve_trace_line >> sub_lit_repr;
        unsigned positive_diff = 
          sub_lit_repr > lit_repr ? 
          sub_lit_repr - lit_repr : 
          lit_repr - sub_lit_repr;
        if(positive_diff != 1)
          current_lit.addSubproof(&lit_proofs[sub_lit_repr]);
      }
    }
    // KEEP: working here
    else if(proof_kind == "CONF:"){
      std::cout << proof_kind << " ";

      // --------------------------
      unsigned clause_id, lit_repr;
      // --------------------------

      resolve_trace_line >> clause_id;
      std::cout << "empty clause: " << clause_id;
      resolve_trace_line >> aux_symbol;
      std::cout << "the lits: ";
      while(resolve_trace_line.good()){
        resolve_trace_line >> lit_repr;
        std::cout << lit_repr << " ";
      }
      std::cout << std::endl;
    }
  }
#if _DEBUG_CLAUSE_PROOF_
  for(auto const & clause_proof : clause_proofs)
    std::cout << clause_proof << std::endl;
#endif
}

void ProofFactory::LitProofs::if_enough_push_back_otherwise_resize(LitProof const & lit_proof){
  if(lit_proof.getId() >= size())
    for(unsigned i = size(); i < lit_proof.getId(); ++i)
      emplace_back(i);
 
  push_back(lit_proof);
}

std::string ProofFactory::exec(const char* cmd) {
    std::array<char, 128> buffer;
    std::string result;
    std::unique_ptr<FILE, decltype(&pclose)> pipe(popen(cmd, "r"), pclose);
    if (!pipe) {
        throw std::runtime_error("popen() failed!");
    }
    while (fgets(buffer.data(), buffer.size(), pipe.get()) != nullptr) {
        result += buffer.data();
    }
    return result.substr(0, result.size() - 1);
}
