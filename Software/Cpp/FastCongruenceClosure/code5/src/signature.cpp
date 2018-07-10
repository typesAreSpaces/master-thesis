#include "signature.h"

signatureArg1::signatureArg1(std::string name, int first) :
  name(name), first(first){}

signatureArg1::~signatureArg1(){}

bool signatureArg1::operator==(const signatureArg1 & x) const {
  return this->name == x.name && this->first == x.first;
}

std::size_t signatureArg1::Hash::operator()(const signatureArg1 & x) const {
  std::size_t res = std::hash<std::string>()(x.name);
  res = res * 31 ^ std::hash<int>()(x.first);
  return res;
}

signatureArg2::signatureArg2(std::string name, int first, int second) :
  name(name), first(first), second(second){}

signatureArg2::~signatureArg2(){}

bool signatureArg2::operator==(const signatureArg2 & x) const {
  return this->name == x.name && this->first == x.first && this->second == x.second;
}

std::size_t signatureArg2::Hash::operator()(const signatureArg2 & x) const {
  std::size_t res = std::hash<std::string>()(x.name);
  res = res * 31 ^ std::hash<int>()(x.first);
  res = res * 31 ^ std::hash<int>()(x.second);
  return res;
}
