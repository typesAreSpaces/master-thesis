#include "traversal.h"

void visit(z3::expr const & e) {
    if (e.is_app()) {
        unsigned num = e.num_args();
        for (unsigned i = 0; i < num; i++) {
            visit(e.arg(i));
        }
        // do something
        // Example: print the visited expression
	z3::func_decl f = e.decl();
        std::cout << "Application of " << f.name() << ": " << e << "\nHash: " << e.hash() <<"\n";
    }
    else if (e.is_quantifier()) {
        visit(e.body());
        // do something
    }
    else { 
        assert(e.is_var());
        // do something
    }
}
