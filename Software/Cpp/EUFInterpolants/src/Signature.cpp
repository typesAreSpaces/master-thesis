#include "Signature.h"

SignatureArg1::SignatureArg1(std::string name,
														 unsigned first_signature) :
  name(name), first_signature(first_signature){}

SignatureArg1::~SignatureArg1(){}

bool SignatureArg1::operator==(const SignatureArg1 & x) const {
  return (this->name == x.name
					&& this->first_signature == x.first_signature);
}

std::ostream & operator << (std::ostream & os, SignatureArg1 & x){
  os << "Signature ";
  os << "Name: " << x.name;
	os << " First_Signature: " << x.first_signature;
  return os;
}

std::size_t SignatureArg1::Hash::operator()(const SignatureArg1 & x) const {
  std::size_t res = std::hash<std::string>()(x.name);
  //res = res * 31 ^ std::hash<int>()(x.first_signature);
  res ^= std::hash<unsigned>()(x.first_signature)
		+ 0x9e3779b9 + (res << 6) + (res >> 2);
  return res;
}

SignatureArg2::SignatureArg2(std::string name,
														 unsigned first_signature, unsigned second_signature) :
  name(name), first_signature(first_signature), second_signature(second_signature){}

SignatureArg2::~SignatureArg2(){}

bool SignatureArg2::operator==(const SignatureArg2 & x) const {
  return (this->name == x.name
					&& this->first_signature == x.first_signature
					&& this->second_signature == x.second_signature);
}

std::ostream & operator << (std::ostream & os, SignatureArg2 & x){
  os << "Signature ";
  os << "Name: " << x.name;
	os << " First_Signature: " << x.first_signature;
	os << " Second_Signature: " << x.second_signature;  
  return os;
}

std::size_t SignatureArg2::Hash::operator()(const SignatureArg2 & x) const {
  std::size_t res = std::hash<std::string>()(x.name);
  res ^= std::hash<unsigned>()(x.first_signature) +
		0x9e3779b9 + (res << 6) + (res >> 2);
  res ^= std::hash<unsigned>()(x.second_signature) +
		0x9e3779b9 + (res << 6) + (res >> 2);
  return res;
}
