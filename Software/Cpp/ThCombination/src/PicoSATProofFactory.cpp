#include "PicoSATProofFactory.h"

PicoProofFactory::PicoResolutionProof::PicoResolutionProof() : 
  pivot(0), subproof_1(-1), subproof_2(-1)
{
  this->resize(0);
}

void PicoProofFactory::PicoResolutionProof::updatePivot(int new_pivot){ pivot = new_pivot; }

void PicoProofFactory::PicoResolutionProof::addLiteral(int literal){ push_back(literal); }

void PicoProofFactory::PicoResolutionProof::updateSubproofs(int new_subproof_1, int new_subproof_2){ 
  subproof_1 = new_subproof_1;
  subproof_2 = new_subproof_2;
}

PicoProofFactory::PicoProofFactory() : 
  proof_table()
{
  std::string current_dir = exec("pwd"), line;

  system(("picosat " + current_dir + "/file.cnf -T proof-temp > /dev/null").c_str());
  //system("picosat /home/jose/Documents/CNF_Files/aim-100-1_6-no-1.cnf -T proof-temp > /dev/null");
  system(("tracecheck " + current_dir + "/proof-temp -B proof > /dev/null").c_str());

  std::ifstream resolve_trace_file(current_dir + "/proof", std::fstream::in);
  unsigned clause_id;
  int literal_id, subproof_1, subproof_2;

  while(std::getline(resolve_trace_file, line)){
    std::istringstream resolve_trace_line(line);

    resolve_trace_line >> clause_id;
    if(clause_id >= proof_table.size())
      proof_table.resize(clause_id + 1);
    proof_table[clause_id] = PicoResolutionProof();
    auto & current_proof_entry = proof_table[clause_id];

    do {
      resolve_trace_line >> literal_id;
      if(literal_id == 0)
        break;
      current_proof_entry.addLiteral(literal_id);
    } while(true);

    resolve_trace_line >> subproof_1;
    if(subproof_1 != 0){
      resolve_trace_line >> subproof_2;
      current_proof_entry.updateSubproofs(subproof_1, subproof_2);
      current_proof_entry.updatePivot(*this);
    }
  }

#if _DEBUG_PICO_SAT_PF_
  std::cout << *this << std::endl;
#endif
}

void PicoProofFactory::PicoResolutionProof::updatePivot(PicoProofFactory const & p){
  std::set<int> values;
  for(auto const & literal : p.proof_table[subproof_1])
    values.insert((literal < 0 ? -literal : literal));
  for(auto const & literal : p.proof_table[subproof_2])
    if(values.find((literal < 0 ? -literal : literal)) != values.end()){
      pivot = literal < 0 ? -literal : literal;
      return;
    }
  throw "Problem @ PicoProofFactory::PicoResolutionProof::updatePivot. Pivot not found";
}

std::ostream & operator << (std::ostream & os, PicoProofFactory const & p){
  unsigned id = 0;
  for(auto const & x : p.proof_table){
    bool is_fact = x.subproof_1 == -1 && x.subproof_2 == -1;
    if(x.size() == 0 && is_fact && ++id)
      continue;
    os << "Id: " << id;
    os << (is_fact ? 
        "(Fact)" : 
        "(Derived(" + std::to_string(x.subproof_1) 
        + "," + std::to_string(x.subproof_2) + "))" ) 
      << " Literals: ";
    for(auto const & literal : x)
      os << literal << " ";
    os << " Pivot: " << x.pivot << std::endl;
    ++id;
  }
  return os;
}

std::string PicoProofFactory::exec(const char* cmd) {
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
