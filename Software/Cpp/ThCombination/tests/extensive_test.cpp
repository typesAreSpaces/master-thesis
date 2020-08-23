#include <functional>
#include <iostream>
#include <fstream>
#include <z3++.h>
#include <vector>
#include "ThCombInterpolatorWithExpressions.h"

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

  //(declare-sort ElementSort 0)
  //(declare-sort ArraySort 0)
  z3::sort element_sort = ctx.uninterpreted_sort("ElementSort");
  z3::sort array_sort = ctx.uninterpreted_sort("ArraySort");
  z3::sort int_sort = ctx.int_sort();
  z3::sort_vector sorts(ctx);
  sorts.push_back(element_sort);
  sorts.push_back(array_sort);
  sorts.push_back(int_sort);

  //(declare-fun e3 () ElementSort)
  //(declare-fun rd (ArraySort Int) ElementSort)
  //(declare-fun i3 () Int)
  //(declare-fun a () ArraySort)
  //(declare-fun i1 () Int)
  //(declare-fun fresh_array_0 () ArraySort)
  //(declare-fun e1 () ElementSort)
  //(declare-fun b () ArraySort)
  //(declare-fun c2 () ArraySort)
  //(declare-fun c1 () ArraySort)
  //(declare-fun fresh_index_1 () Int)
  //(declare-fun fresh_index_2 () Int)
  //(declare-fun i2 () Int)
  z3::func_decl_vector func_decls(ctx);
  func_decls.push_back(ctx.function("e3", 0, 0, element_sort));
  func_decls.push_back(ctx.function("rd", array_sort, int_sort, element_sort));
  func_decls.push_back(ctx.function("i3", 0, 0, int_sort));
  func_decls.push_back(ctx.function("a", 0, 0, array_sort));
  func_decls.push_back(ctx.function("i1", 0, 0, int_sort));
  func_decls.push_back(ctx.function("fresh_array_0", 0, 0, array_sort));
  func_decls.push_back(ctx.function("e1", 0, 0, element_sort));
  func_decls.push_back(ctx.function("b", 0, 0, array_sort));
  func_decls.push_back(ctx.function("c2", 0, 0, array_sort));
  func_decls.push_back(ctx.function("c1", 0, 0, array_sort));
  func_decls.push_back(ctx.function("fresh_index_1", 0, 0, int_sort));
  func_decls.push_back(ctx.function("fresh_index_2", 0, 0, int_sort));
  func_decls.push_back(ctx.function("i2", 0, 0, int_sort));

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

  unsigned limit = 10;

  for(auto const & form_a : part_a_forms)
    for(auto const & form_b : part_b_forms){
      // TODO: normalize expressions with not's
      try {
        ThCombInterpolatorWithExpressions test(form_a, form_b);
        std::cout << test << std::endl;
      }
      catch(char const * e){
        std::cerr << e << std::endl;
      }
      if(!--limit)
        return;
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
      results.push_back(ctx.parse_string(
            accum.c_str(), 
            sorts, func_decls));
    }

    if(flag)
      accum += "(assert " + line + ")";
    else
      accum = "";

    if(line.find("goal") != std::string::npos)
      flag = true;
  }
  return results;
}

