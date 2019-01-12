#include <iostream>
#include <fstream>
#include <cstdlib>
#include <ctime>

#include "EUFInterpolant.h"
#include "Declarations.h"
//#include "z3++.h"

// class Declarations {
// private:
// 	z3::context &              ctx;
// 	std::vector<std::string>   names;
// 	std::vector<z3::sort>      sorts;
// 	std::vector<z3::func_decl> funs;
// 	std::vector<z3::expr>      todo;
// 	std::set<unsigned>         seen_ids;
// 	inline bool contains_id(unsigned) const;
// 	void collect_decls(z3::expr &);
// 	void collect_sort(const z3::sort &);
// 	void collect_func(const z3::func_decl &);
// 	std::string lower_case_fun(z3::symbol const &);
// 	std::string sanitize(z3::symbol const &);
// public:
// 	Declarations(z3::context &, z3::expr &);
// 	~Declarations();
// 	void display_func_decl(std::ostream &, z3::func_decl &);
// 	void display_sort(std::ostream &, z3::sort const &);
// 	void display_sort_decls(std:: ostream &);
// 	void display_sort_decl(std::ostream & , z3::sort &);
// 	void display_func_decls(std::ostream &);
// };

int main(int argc, char ** argv){
	
	// Testing EUFInterpolant algorithm
  std::string file = "./tests/smt2lib_2/kapurEUFExample2_5.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_firewire_tree.3.prop2_ab_reg_max.smt2";
  //std::string file = "/Users/joseabelcastellanosjoo/Documents/QF_UF/2018-Goel-hwbench/QF_UF_needham.3.prop4_ab_reg_max.smt2";

  z3::config cfg;
  cfg.set("PROOF", true);
  cfg.set("MODEL", true);
  cfg.set("TRACE", false);
  z3::context ctx(cfg);
	
	// I'm using Z3_ast_vector_get
	// because parsing from a file using 
	// Z3, the API only provides 
	// the function Z3_parse_smtlib2_file
	// which returns a Z3_ast_vector
	Z3_ast_vector conjunction_of_assertions =
		Z3_parse_smtlib2_file(ctx, file.c_str(), 0, 0, 0, 0, 0, 0);
  Z3_ast input_formula =
		Z3_ast_vector_get(ctx, conjunction_of_assertions, 0);
	z3::expr input_formula_expr(ctx, input_formula);
  std::set<std::string> symbols_to_elim = {"f"};
	
  EUFInterpolant eufI (ctx, input_formula, symbols_to_elim);
  eufI.algorithm();

	std::cout << std::endl;
	
	// Declarations decls (ctx, input_formula_expr);
	// std::cout << "Sort Declarations" << std::endl;
	// decls.display_sort_decls(std::cout);
	// std::cout << std::endl;
	// std::cout << "Func Declarations" << std::endl;
	// decls.display_func_decls(std::cout);

	// ---------------------------------------------------------
	// The following code shows how to construct
	// new terms using the z3++ api. We notice
	// the context does not allow symbol duplication
	// Test used:
	// "./tests/smt2lib_2/kapurEUFExample2_4.smt2"
	// ---------------------------------------------------------
	// z3::sort _sort = ctx.uninterpreted_sort("A");
	// z3::expr x = ctx.constant("x1", _sort);
	// z3::func_decl f = z3::function("f", _sort, _sort, _sort);
	// z3::expr f_x_x = f(x, x);
	// std::cout << "Input formula\n";
	// std::cout << input_formula_expr << std::endl;
	// std::cout << x << std::endl;

	// std::cout << "Ids" << std::endl;
	// std::cout << Z3_get_ast_id(ctx, x) << std::endl;

	// std::cout << f_x_x << std::endl;
	// std::cout << Z3_get_ast_id(ctx, f_x_x) << std::endl;

	// ---------------------------------------------------------
	// The following code shows how to construct
	// new terms using the z3++ api. We notice
	// the context does not allow symbol duplication
	// Test used:
	// "./tests/smt2lib_2/kapurEUFExample2_5.smt2"
	// ---------------------------------------------------------
	// z3::sort _sort = ctx.uninterpreted_sort("A");
	// z3::sort_vector _sorts(ctx);
	// _sorts.push_back(_sort), _sorts.push_back(_sort), _sorts.push_back(_sort);
	// z3::func_decl f  = z3::function("f", _sorts, _sort);
	// z3::expr x1 = ctx.constant("x1", _sort);
	// z3::expr f_x1_x1_x1 = f(x1, x1, x1);
	// z3::expr x2 = ctx.constant("x2", _sort);
	// z3::expr f_x1_x2_x1 = f(x1, x2, x1);

	// std::cout << f_x1_x1_x1 << std::endl;
	// std::cout << Z3_get_ast_id(ctx, f_x1_x1_x1) << std::endl;
	// std::cout << f_x1_x2_x1 << std::endl;
	// std::cout << Z3_get_ast_id(ctx, f_x1_x2_x1) << std::endl;
	// std::cout << x2 << std::endl;
	// std::cout << Z3_get_ast_id(ctx, x2) << std::endl;
	
  return 0;
}

// Declarations::Declarations(z3::context & ctx, z3::expr & formula) :
// 	ctx(ctx) {
// 	collect_decls(formula);
// }

// Declarations::~Declarations() {}

// void Declarations::display_func_decl(std::ostream & out, z3::func_decl & f) {
// 	std::string name = lower_case_fun(f.name());
// 	out << "tff(" << name << "_type, type, (\n   " << name << ": ";
// 	unsigned na = f.arity();
// 	switch(na) {
// 	case 0:
// 		break;
// 	case 1: {
// 		z3::sort s(f.domain(0));
// 		display_sort(out, s);
// 		out << " > ";
// 		break;
// 	}
// 	default:
// 		out << "( ";
// 		for (unsigned j = 0; j < na; ++j) {
// 			z3::sort s(f.domain(j));
// 			display_sort(out, s);
// 			if (j + 1 < na) {
// 				out << " * ";
// 			}
// 		}
// 		out << " ) > ";
// 	}
// 	z3::sort srt(f.range());
// 	display_sort(out, srt);
// 	out << ")).\n";
// }

// void Declarations::display_sort(std::ostream& out, z3::sort const& s) {
// 	if (s.is_int()) {
// 		out << "$int";
// 	}
// 	else if (s.is_real()) {
// 		out << "$real";
// 	}
// 	else if (s.is_bool()) {
// 		out << "$o";
// 	}
// 	else {
// 		out << s;
// 	}
// }

// void Declarations::display_sort_decls(std::ostream& out) {
// 	for (unsigned i = 0; i < sorts.size(); ++i) {
// 		display_sort_decl(out, sorts[i]);
// 	}
// }
    
// void Declarations::display_sort_decl(std::ostream& out, z3::sort& s) {
// 	out << "tff(" << s << "_type, type, (" << s << ": $tType)).\n";
// }


// void Declarations::display_func_decls(std::ostream& out) {
// 	for (size_t i = 0; i < funs.size(); ++i) {
// 		display_func_decl(out, funs[i]);
// 	}
// }

// bool Declarations::contains_id(unsigned id) const {
// 	return seen_ids.find(id) != seen_ids.end();
// }

// void Declarations::collect_decls(z3::expr & e) {
// 	todo.push_back(e);
// 	while (!todo.empty()) {
// 		z3::expr e = todo.back();
// 		todo.pop_back();
// 		unsigned id = Z3_get_ast_id(ctx, e);
// 		if (contains_id(id)) {
// 			continue;
// 		}
// 		seen_ids.insert(id);
// 		if (e.is_app()) {
// 			collect_func(e.decl());
// 			unsigned sz = e.num_args();
// 			for (unsigned i = 0; i < sz; ++i) {
// 				todo.push_back(e.arg(i));
// 			}
// 		}
// 		else if (e.is_quantifier()) {
// 			unsigned nb = Z3_get_quantifier_num_bound(e.ctx(), e);
// 			for (unsigned i = 0; i < nb; ++i) {
// 				z3::sort srt(ctx, Z3_get_quantifier_bound_sort(e.ctx(), e, i));
// 				collect_sort(srt);
// 			}
// 			todo.push_back(e.body());
// 		}
// 		else if (e.is_var()) {
// 			collect_sort(e.get_sort());
// 		}
// 	}
// }

// void Declarations::collect_sort(const z3::sort & s) {
// 	unsigned id = Z3_get_sort_id(ctx, s);
// 	// if (s.sort_kind() == Z3_UNINTERPRETED_SORT && 
// 	// 		contains_id(id)) {
// 	// We add the sort
// 	// if it hasn't been 
// 	// seen before
// 	if (!contains_id(id)) {
// 		seen_ids.insert(id);
// 		sorts.push_back(s);
// 	}
// }

// void Declarations::collect_func(const z3::func_decl & f) {
// 	unsigned id = Z3_get_func_decl_id(ctx, f);
// 	if (contains_id(id)) {
// 		return;
// 	}
// 	seen_ids.insert(id);
// 	if (f.decl_kind() == Z3_OP_UNINTERPRETED) {
// 		funs.push_back(f);
// 	}
// 	for (unsigned i = 0; i < f.arity(); ++i) {
// 		collect_sort(f.domain(i));
// 	}
// 	collect_sort(f.range());
// }

// std::string Declarations::lower_case_fun(z3::symbol const& sym) {
// 	std::string result = sanitize(sym);
// 	char ch = result[0];
// 	if ('a' <= ch && ch <= 'z') {
// 		return result;
// 	}
// 	else {
// 		return "tptp_fun_" + result;
// 	}
// }

// std::string Declarations::sanitize(z3::symbol const& sym) {
// 	std::ostringstream str;
// 	if (sym.kind() == Z3_INT_SYMBOL) {
// 		str << sym;
// 		return str.str();
// 	}
// 	std::string s = sym.str();
// 	size_t sz = s.size();
// 	for (size_t i = 0; i < sz; ++i) {
// 		char ch = s[i];
// 		if ('a' <= ch && ch <= 'z') {
// 			str << ch;
// 		}
// 		else if ('A' <= ch && ch <= 'Z') {
// 			str << ch;
// 		}
// 		else if ('0' <= ch && ch <= '9') {
// 			str << ch;
// 		}
// 		else if ('_' == ch) {
// 			str << ch;
// 		}
// 		else {
// 			str << "_";
// 		}
// 	}
// 	return str.str();
// }
