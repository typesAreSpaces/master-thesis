// #include "Declarations.h"

// Declarations::Declarations(z3::context & ctx, z3::expr & formula) :
// 	ctx(ctx), formula(formula){
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
// 	if (s.sort_kind() == Z3_UNINTERPRETED_SORT && 
// 			contains_id(id)) {
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
