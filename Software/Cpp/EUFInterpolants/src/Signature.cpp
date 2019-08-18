#include "Signature.h"

UnarySignature::UnarySignature(std::string name,
			       unsigned first_signature) :
  name(name), first_signature(first_signature){}

UnarySignature::~UnarySignature(){}

bool UnarySignature::operator==(const UnarySignature & x) const {
  return (this->name == x.name
	  && this->first_signature == x.first_signature);
}

std::ostream & operator << (std::ostream & os, UnarySignature & x){
  os << "Signature ";
  os << "Name: " << x.name;
  os << " First_Signature: " << x.first_signature;
  return os;
}

std::size_t UnarySignature::Hash::operator()(const UnarySignature & x) const {
  std::size_t res = std::hash<std::string>()(x.name);
  //res = res * 31 ^ std::hash<int>()(x.first_signature);
  res ^= std::hash<unsigned>()(x.first_signature)
    + 0x9e3779b9 + (res << 6) + (res >> 2);
  return res;
}

BinarySignature::BinarySignature(std::string name,
				 unsigned first_signature, unsigned second_signature) :
  name(name), first_signature(first_signature), second_signature(second_signature){}

BinarySignature::~BinarySignature(){}

bool BinarySignature::operator==(const BinarySignature & x) const {
  return (this->name == x.name
	  && this->first_signature == x.first_signature
	  && this->second_signature == x.second_signature);
}

std::ostream & operator << (std::ostream & os, BinarySignature & x){
  os << "Signature ";
  os << "Name: " << x.name;
  os << " First_Signature: " << x.first_signature;
  os << " Second_Signature: " << x.second_signature;  
  return os;
}

std::size_t BinarySignature::Hash::operator()(const BinarySignature & x) const {
  std::size_t res = std::hash<std::string>()(x.name);
  res ^= std::hash<unsigned>()(x.first_signature) +
    0x9e3779b9 + (res << 6) + (res >> 2);
  res ^= std::hash<unsigned>()(x.second_signature) +
    0x9e3779b9 + (res << 6) + (res >> 2);
  return res;
}
