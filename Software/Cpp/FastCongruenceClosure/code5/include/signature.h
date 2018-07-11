#ifndef _SIGNATURES_
#define _SIGNATURES_

#include <iostream>

struct signatureArg1 {
  std::string name;
  int first;
  struct Hash;
  signatureArg1(std::string, int);
  ~signatureArg1();
  bool operator==(const signatureArg1 &) const;
  friend std::ostream & operator << (std::ostream &, signatureArg1 &);
};

struct signatureArg1::Hash {
  std::size_t operator()(const signatureArg1 &) const;
};

struct signatureArg2 {
  std::string name;
  int first, second;
  struct Hash;
  signatureArg2(std::string, int, int);
  ~signatureArg2();
  bool operator==(const signatureArg2 &) const;
  friend std::ostream & operator << (std::ostream &, signatureArg2 &);
};

struct signatureArg2::Hash {
  std::size_t operator()(const signatureArg2 &) const;
};

#endif