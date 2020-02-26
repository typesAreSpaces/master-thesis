#ifndef _CONG_CLOSURE__
#define _CONG_CLOSURE_
#define DEBUG_DESTRUCTORS_CC true

#include <iostream>
#include <unordered_map>
#include <list>
#include <utility>
#include <z3++.h>
#include "UnionFind.h"

class SignatureTable {
  std::unordered_map<std::size_t, unsigned> sig_table;
  UnionFind & uf;
  std::hash<std::string> hash_string;
  std::hash<unsigned> hash_unsigned;

  std::size_t hash_z3expr(const z3::expr & e){
    unsigned num_args = e.num_args();
    std::string name = e.decl().name().str();
    std::size_t seed = hash_string(name);
    seed ^= hash_unsigned(num_args) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    for(unsigned i = 0; i < num_args; i++)
      seed ^= hash_unsigned(uf.find(e.arg(i).id())) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
    return seed;
  }
public:
  SignatureTable(UnionFind & uf) : uf(uf){}
  ~SignatureTable(){
#if DEBUG_DESTRUCTORS_CC
    std::cout << "Done ~SignatureTable" << std::endl;
#endif
  }
  void enter(const z3::expr & e){
    sig_table[hash_z3expr(e)] = e.id();
  }
  void erase(const z3::expr & e){
    sig_table.erase(hash_z3expr(e));
  }
  unsigned query(const z3::expr & e){
    auto r = sig_table.find(hash_z3expr(e));
    if(r == sig_table.end())
      throw "Element not in the table";
    return r->second;
  }
  friend std::ostream & operator << (std::ostream & os, const SignatureTable & st){
    return os;
  }
};

typedef std::vector<std::list<unsigned> > CCList;

class CongruenceClosure {
  const z3::expr_vector & terms;
  CCList &                cc_list;
  UnionFind &             uf;
  SignatureTable          sig_table;
 public:
  CongruenceClosure(const z3::expr_vector &, CCList &, UnionFind &);
  void buildCongruenceClosure(std::list<unsigned> &, std::list<std::pair<unsigned, unsigned> > &);
  ~CongruenceClosure();
  friend std::ostream & operator << (std::ostream &, const CongruenceClosure &);
};


#endif
