#include "ProofFactory.h"
#include <ostream>

ResolutionProof::ResolutionProof() :
  pivots({})
{
}

void ResolutionProof::addPivot(unsigned pivot){
  pivots.push_back(pivot);
}

ClauseProof::ClauseProof(unsigned id) : 
  ResolutionProof(),
  id(id), literals({}), clause_subproofs({})
{
}

void ClauseProof::addLiteral(int lit){
  literals.push_back(lit);
}

void ClauseProof::addSubproof(ClauseProof const * subproof){
  clause_subproofs.push_back(subproof);
}

void ClauseProof::setLiterals(ClauseProof const & clause_proof){
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
  os << " pivots: ";
  for(auto const & x : cp.pivots)
    os << x << " ";
  return os;
}

LitProof::LitProof(unsigned id) : 
  ResolutionProof(), 
  id(id), lit_subproofs({}), clause_subproof(nullptr)
{
}

unsigned LitProof::getId() const {
  return id;
}

void LitProof::addSubproof(LitProof const * lit_proof){
  lit_subproofs.push_back(lit_proof);
}

void LitProof::setClauseProof(ClauseProof const * clause_proof){
  clause_subproof = clause_proof;
}

std::ostream & operator << (std::ostream & os, LitProof const & lp){
  os << "var id: " 
    << (lp.id % 2 == 0 ? ""      : "-")
    << (lp.id % 2 == 0 ? lp.id/2 : (lp.id - 1)/2);
  os << " lit subproofs: ";
  for(auto const & x : lp.lit_subproofs)
    os << x->getId() << " ";
  os << " pivots: ";
  for(auto const & x : lp.pivots)
    os << x << " ";
  return os;
}

ConflictProof::ConflictProof():
  ResolutionProof(),
  lit_subproofs({}), clause_subproof(nullptr)
{
}

void ConflictProof::addSubproof(LitProof const * lit_proof){
  lit_subproofs.push_back(lit_proof);
}

void ConflictProof::setClauseProof(ClauseProof const * clause_proof){
  clause_subproof = clause_proof;
}

std::ostream & operator << (std::ostream & os, ConflictProof const & conp){
  os << "conflict clause";
  os << " pivots: ";
  for(auto const & x : conp.pivots)
    os << x << " ";
  return os;
}

ProofFactory::ProofFactory():
  clause_proofs(), lit_proofs(), conflict_proof()
{
  std::string current_dir = exec("pwd");

  //std::ifstream cnf_file("/home/jose/booleforce_examples/hole6.cnf", std::fstream::in);
  std::ifstream cnf_file(current_dir + "/file.cnf", std::fstream::in);
  std::string line;
  std::getline(cnf_file, line);
  // Setup literals
  std::string header_symbols;
  unsigned num_vars;
  std::istringstream lits_line(line);
  lits_line >> line >> line >> num_vars;
  initLitProofs(2*num_vars + 2);

  // Setup initial clauses
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

  //system("zchaff ~/booleforce_examples/hole6.cnf > /dev/null");
  system(("zchaff " + current_dir + "/file.cnf > /dev/null").c_str());

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

      resolve_trace_line 
        >> clause_id >> aux_symbol 
        >> pivot_id >> sub_clause_id;

      clause_proofs.emplace_back(clause_id);
      auto & lhs_clause = clause_proofs[clause_id];
      lhs_clause.addSubproof(&clause_proofs[sub_clause_id]);
      lhs_clause.setLiterals(clause_proofs[sub_clause_id]);
      do {
        resolve_trace_line >> pivot_id; 
        resolve_trace_line >> sub_clause_id;
        lhs_clause.addSubproof(&clause_proofs[sub_clause_id]);
        lhs_clause.updateResolution(pivot_id, clause_proofs[sub_clause_id]);
        lhs_clause.addPivot((pivot_id < 0 ? -pivot_id : pivot_id ));
      } while(resolve_trace_line.good());
    }
    else if(proof_kind == "VAR:"){
      // ------------------------------------------------
      unsigned pure_literal, aux_number, polarity, 
               antecedent_clause, lit_repr, sub_lit_repr;
      // ------------------------------------------------

      resolve_trace_line >> pure_literal
        >> aux_symbol
        >> aux_number
        >> aux_symbol
        >> polarity
        >> aux_symbol
        >> antecedent_clause
        >> aux_symbol;

      lit_repr = polarity ? 2*pure_literal : 2*pure_literal + 1;
      LitProof & current_lit = lit_proofs[lit_repr];
      current_lit.setClauseProof(&clause_proofs[antecedent_clause]);
      while(resolve_trace_line.good()){
        resolve_trace_line >> sub_lit_repr;
        if(sub_lit_repr != lit_repr){
          current_lit.addPivot(
              (sub_lit_repr % 2 == 0 ? (int)(sub_lit_repr/2) : (int)((sub_lit_repr - 1)/2))
              );
          current_lit.addSubproof(&lit_proofs[
              (sub_lit_repr % 2 == 0 ? sub_lit_repr + 1 : sub_lit_repr - 1)
          ]);
        }
      }
    }
    else if(proof_kind == "CONF:"){
      // ------------------------------
      unsigned clause_id, sub_lit_repr;
      // ------------------------------

      resolve_trace_line >> clause_id
        >> aux_symbol;
      conflict_proof.setClauseProof(&clause_proofs[clause_id]);
      while(resolve_trace_line.good()){
        resolve_trace_line >> sub_lit_repr;
        conflict_proof.addPivot(
            (sub_lit_repr % 2 == 0 ? (int)(sub_lit_repr/2) : (int)((sub_lit_repr - 1)/2))
            );
        conflict_proof.addSubproof(&lit_proofs[
            (sub_lit_repr % 2 == 0 ? sub_lit_repr + 1 : sub_lit_repr - 1)
        ]);
      }
    }
  }
#if _DEBUG_CLAUSE_PROOF_
  for(auto const & clause_proof : clause_proofs)
    std::cout << clause_proof << std::endl;
  for(auto const & lit_proof : lit_proofs)
    std::cout << lit_proof << std::endl;
  std::cout << conflict_proof << std::endl;
#endif
}

void ProofFactory::initLitProofs(unsigned num_vars){
  for(unsigned i = 0; i < num_vars; ++i)
    lit_proofs.emplace_back(i);
}

std::ostream & operator << (std::ostream & os, ProofFactory const & pf){
  os << std::endl << "Clause proofs" << std::endl;
  for(auto const & x : pf.clause_proofs)
    os << x << std::endl;
  os << std::endl << "Lit proofs" << std::endl;
  for(auto const & x : pf.lit_proofs)
    os << x << std::endl;
  os << std::endl << "Conflict Proof" << std::endl;
  os << pf.conflict_proof << std::endl;
  return os;
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
