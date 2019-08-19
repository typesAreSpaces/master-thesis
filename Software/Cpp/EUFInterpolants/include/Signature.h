#ifndef _SIGNATURES_
#define _SIGNATURES_

#include <iostream>

struct UnarySignature {
  const std::string & name;
  unsigned            first_signature;
  struct Hash;
  UnarySignature(const std::string &, unsigned);
  ~UnarySignature();
  bool operator==(const UnarySignature &) const;
  friend std::ostream & operator << (std::ostream &, const UnarySignature &);
};

struct UnarySignature::Hash {
  std::size_t operator()(const UnarySignature &) const;
};

struct BinarySignature {
  const std::string & name;
  unsigned            first_signature, second_signature;
  struct Hash;
  BinarySignature(const std::string &, unsigned, unsigned);
  ~BinarySignature();
  bool operator==(const BinarySignature &) const;
  friend std::ostream & operator << (std::ostream &, const BinarySignature &);
};

struct BinarySignature::Hash {
  std::size_t operator()(const BinarySignature &) const;
};

#endif
