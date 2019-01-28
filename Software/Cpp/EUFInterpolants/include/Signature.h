#ifndef _SIGNATURES_
#define _SIGNATURES_

#include <iostream>

struct SignatureArg1 {
  std::string name;
  unsigned    first_signature;
  struct Hash;
  SignatureArg1(std::string, unsigned);
  ~SignatureArg1();
  bool operator==(const SignatureArg1 &) const;
  friend std::ostream & operator << (std::ostream &, SignatureArg1 &);
};

struct SignatureArg1::Hash {
  std::size_t operator()(const SignatureArg1 &) const;
};

struct SignatureArg2 {
  std::string name;
  unsigned    first_signature, second_signature;
  struct Hash;
  SignatureArg2(std::string, unsigned, unsigned);
  ~SignatureArg2();
  bool operator==(const SignatureArg2 &) const;
  friend std::ostream & operator << (std::ostream &, SignatureArg2 &);
};

struct SignatureArg2::Hash {
  std::size_t operator()(const SignatureArg2 &) const;
};

#endif
