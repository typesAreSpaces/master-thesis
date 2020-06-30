#include "ResolutionProof.h"

ResolutionProof::ResolutionProof()
{
  std::string current_dir = exec("pwd");
  system(("zchaff " + current_dir + "/file.cnf > /dev/null").c_str());
  std::ifstream resolve_trace_file((current_dir + "/resolve_trace"), std::fstream::in);
  std::string line, proof_kind, aux_symbol;

  while(std::getline(resolve_trace_file, line)){
    std::istringstream resolve_trace_line(line);
    resolve_trace_line >> proof_kind;

    if(proof_kind == "CL:"){
      std::cout << proof_kind << " ";

      // --------------------
      unsigned clause_id;
      int pivot_id;
      // --------------------

      resolve_trace_line >> clause_id;
      std::cout << "clause_id: " << clause_id << " ";
      resolve_trace_line >> aux_symbol;

      std::cout << "resolution chain: ";
      while(resolve_trace_line.good()){
        resolve_trace_line >> pivot_id; 
        resolve_trace_line >> clause_id;
        std::cout << pivot_id << " ";
        std::cout << clause_id << " ";
      }
    }
    else if(proof_kind == "VAR:"){
      std::cout << proof_kind << " ";

      // ----------------------------------------------------------------------
      unsigned pure_literal, aux_number, polarity, antecedent_clause, lit_repr;
      // ----------------------------------------------------------------------

      resolve_trace_line >> pure_literal;
      std::cout << "the lit: " << pure_literal << " ";
      resolve_trace_line >> aux_symbol;
      resolve_trace_line >> aux_number;
      resolve_trace_line >> aux_symbol;
      resolve_trace_line >> polarity;
      std::cout << "polarity: " << polarity << " ";
      resolve_trace_line >> aux_symbol;
      resolve_trace_line >> antecedent_clause;
      std::cout << "antecedent_clause: " << antecedent_clause << " ";
      resolve_trace_line >> aux_symbol;
      std::cout << "lits: ";
      while(resolve_trace_line.good()){
        resolve_trace_line >> lit_repr;
        std::cout << lit_repr << " ";
      }
    }
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
    }
    std::cout << std::endl;
  }

}


std::string ResolutionProof::exec(const char* cmd) {
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

