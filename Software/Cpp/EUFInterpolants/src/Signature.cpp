#include "Signature.h"

signatureArg1::signatureArg1(std::string name,
														 unsigned first_signature) :
  name(name), first_signature(first_signature){}

signatureArg1::~signatureArg1(){}

bool signatureArg1::operator==(const signatureArg1 & x) const {
  return (this->name == x.name
					&& this->first_signature == x.first_signature);
}

std::ostream & operator << (std::ostream & os, signatureArg1 & x){
  os << "Signature ";
  os << "Name: " << x.name;
	os << " First_Signature: " << x.first_signature;
  return os;
}

std::size_t signatureArg1::Hash::operator()(const signatureArg1 & x) const {
  std::size_t res = std::hash<std::string>()(x.name);
  //res = res * 31 ^ std::hash<int>()(x.first_signature);
  res ^= std::hash<unsigned>()(x.first_signature) + 0x9e3779b9 + (res << 6) + (res >> 2);
  return res;
}

signatureArg2::signatureArg2(std::string name,
														 unsigned first_signature, unsigned second_signature) :
  name(name), first_signature(first_signature), second_signature(second_signature){}

signatureArg2::~signatureArg2(){}

bool signatureArg2::operator==(const signatureArg2 & x) const {
  return (this->name == x.name
					&& this->first_signature == x.first_signature
					&& this->second_signature == x.second_signature);
}

std::ostream & operator << (std::ostream & os, signatureArg2 & x){
  os << "Signature ";
  os << "Name: " << x.name;
	os << " First_Signature: " << x.first_signature;
	os << " Second_Signature: " << x.second_signature;  
  return os;
}

std::size_t signatureArg2::Hash::operator()(const signatureArg2 & x) const {
  std::size_t res = std::hash<std::string>()(x.name);
  res ^= std::hash<unsigned>()(x.first_signature) + 0x9e3779b9 + (res << 6) + (res >> 2);
  res ^= std::hash<unsigned>()(x.second_signature) + 0x9e3779b9 + (res << 6) + (res >> 2);
  return res;
}
