#include "Signature.h"

signatureArg1::signatureArg1(std::string name, unsigned first) :
  name(name), first(first){}

signatureArg1::~signatureArg1(){}

bool signatureArg1::operator==(const signatureArg1 & x) const {
  return this->name == x.name && this->first == x.first;
}

std::ostream & operator << (std::ostream & os, signatureArg1 & x){
  os << "Signature ";
  os << "Name: " << x.name << " First: " << x.first;  
  return os;
}

std::size_t signatureArg1::Hash::operator()(const signatureArg1 & x) const {
  std::size_t res = std::hash<std::string>()(x.name);
  //res = res * 31 ^ std::hash<int>()(x.first);
  res ^= std::hash<unsigned>()(x.first) + 0x9e3779b9 + (res << 6) + (res >> 2);
  return res;
}

signatureArg2::signatureArg2(std::string name, unsigned first, unsigned second) :
  name(name), first(first), second(second){}

signatureArg2::~signatureArg2(){}

bool signatureArg2::operator==(const signatureArg2 & x) const {
  return this->name == x.name && this->first == x.first && this->second == x.second;
}

std::ostream & operator << (std::ostream & os, signatureArg2 & x){
  os << "Signature ";
  os << "Name: " << x.name << " First: " << x.first << " Second: " << x.second;  
  return os;
}

std::size_t signatureArg2::Hash::operator()(const signatureArg2 & x) const {
  std::size_t res = std::hash<std::string>()(x.name);
  res ^= std::hash<unsigned>()(x.first) + 0x9e3779b9 + (res << 6) + (res >> 2);
  res ^= std::hash<unsigned>()(x.second) + 0x9e3779b9 + (res << 6) + (res >> 2);
  return res;
}
