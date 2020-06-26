#ifndef _PURIFIER_
#define _PURIFIER_
#define _DEBUG_SHARING_ 0

#include <iostream>
#include <z3++.h>
#include <string>
#include <map>
#include <vector>

// Accepts a *conjunction* of literals
// in QF_UFLIA

class Purifier {

  typedef unsigned Z3_EXPR_ID;
  typedef unsigned OCT_FRESH_ID;
  typedef unsigned EUF_FRESH_ID;
  typedef std::map<Z3_EXPR_ID, z3::expr const> SharingMap;

protected:
  static unsigned fresh_var_id;

  z3::context & ctx;
  
  z3::expr_vector oct_component;
  z3::expr_vector euf_component;

  z3::expr_vector shared_variables;

  std::map<Z3_EXPR_ID, OCT_FRESH_ID> oct_fresh_ids;
  std::map<Z3_EXPR_ID, EUF_FRESH_ID> euf_fresh_ids;

  z3::expr_vector       from;
  z3::expr_vector       to;
  z3::expr_vector const input;

private:  
  z3::expr_vector purify(z3::expr_vector const &);
  z3::expr purify(z3::expr const &);
  z3::expr traverse(z3::expr const &);
  z3::expr purifyOctagonTerm(z3::expr const &);
  z3::expr purifyEUFTerm(z3::expr const &);

  void split(z3::expr const &);
  void split(z3::expr_vector const &);
  void update_shared_vars();
  void aux_update_shared_vars(z3::expr const &, SharingMap &);
  
public:
  Purifier(z3::expr_vector const &);

  void addEufFormulasToSolver(z3::solver &); // TODO: Why do I need this function?
  void addOctFormulasToSolver(z3::solver &); // TODO: Why do I need this function?
  bool inside(z3::expr const &);             // TODO: Why do I need this function?
  z3::expr_vector const getSharedVariables() const;
  
  friend std::ostream & operator << (std::ostream &, Purifier &);
};

#endif
