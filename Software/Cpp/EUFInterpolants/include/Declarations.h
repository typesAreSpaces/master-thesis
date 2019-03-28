#ifndef _DECLARATIONS_
#define _DECLARATIONS_

#include <iostream>
#include <vector>
#include <set>
#include "z3++.h"

class Declarations {
private:
	z3::context &              ctx;
	std::vector<std::string>   names;
	std::vector<z3::sort>      sorts;
	std::vector<z3::func_decl> funs;
	std::vector<z3::expr>      todo;
	std::set<unsigned>         seen_ids;
	inline bool contains_id(unsigned) const;
	void collect_decls(z3::expr &);
	void collect_sort(const z3::sort &);
	void collect_func(const z3::func_decl &);
	std::string lower_case_fun(z3::symbol const &);
	std::string sanitize(z3::symbol const &);
	
public:
	Declarations(z3::context &, z3::expr &);
	~Declarations();
	void display_func_decl(std::ostream &, z3::func_decl &);
	void display_sort(std::ostream &, z3::sort const &);
	void display_sort_decls(std:: ostream &);
	void display_sort_decl(std::ostream & , z3::sort &);
	void display_func_decls(std::ostream &);
	std::vector<std::string> getNames();
	std::vector<z3::sort> getSorts();
	std::vector<z3::func_decl> getFunctions();
};

#endif
