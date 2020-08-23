#include <functional>
#include <iostream>
#include <fstream>
#include <z3++.h>
#include <vector>

void crossTest(z3::context &, 
    z3::sort_vector const &, 
    z3::func_decl_vector const &, 
    char *, char*);
std::vector<z3::expr_vector> parseStream(
    z3::context &, 
    z3::sort_vector const &, 
    z3::func_decl_vector const &, 
    char *);
int main(int, char **);

int main(int argc, char * argv[]){
  z3::context ctx;
  // TODO: figure out how to obtain these
  z3::sort_vector sorts(ctx);
  z3::func_decl_vector func_decls(ctx);
  switch(argc){
    case 3:
      crossTest(ctx, sorts, func_decls, argv[1], argv[2]);
      return 0;
    default:
      std::cerr << "bad input" << std::endl;
      return 1;
  }
}

void crossTest(z3::context & ctx, 
    z3::sort_vector const & sorts,
    z3::func_decl_vector const & func_decls,
    char * part_a_goals_file_name, 
    char * part_b_goals_file_name){
  
  std::vector<z3::expr_vector> part_a_forms = parseStream(ctx, sorts, func_decls, part_a_goals_file_name);
  std::vector<z3::expr_vector> part_b_forms = parseStream(ctx, sorts, func_decls, part_b_goals_file_name); 

  for(auto const & form_a : part_a_forms)
    for(auto const & form_b : part_b_forms){
      // TODO: implement the following
      std::cout << "Do something with " << std::endl;
      std::cout << form_a << " and " << form_b << std::endl;
    }

} 

std::vector<z3::expr_vector> parseStream(
    z3::context & ctx, 
    z3::sort_vector const & sorts,
    z3::func_decl_vector const & func_decls,
    char * file_name){
  std::vector<z3::expr_vector> results;
  z3::expr_vector goals(ctx);
  std::ifstream stream(file_name);
  std::string line, accum = "";
  bool flag = false;

  // First line (goals
  std::getline(stream, line);

  while(line[0] != ')'){
    std::getline(stream, line);

    if(line.find("precision") != std::string::npos){
      flag = false;
#if 1
      std::cout << "processed " << accum << std::endl;
#endif
#if 0
      results.push_back(ctx.parse_string(
            ("(assert " + accum + ")").c_str(), 
            sorts, func_decls));
#endif
    }

    if(flag)
      accum += line;
    else
      accum = "";

    if(line.find("goal") != std::string::npos)
      flag = true;
  }
  return results;
}

