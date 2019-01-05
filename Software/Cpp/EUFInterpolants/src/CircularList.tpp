template <typename T>
void CircularList<T>::addEmpty(T x){
  node<T> * temp = new node<T>;
  temp->data = x;
  temp->next = temp;
	list = temp;
}

template <typename T>
void CircularList<T>::addNonEmpty(T x){
  node<T> * temp = new node<T>;
  temp->data = x;
	temp->next = list->next;
  list->next = temp;
	list = temp;
}

template <typename T>
CircularList<T>::CircularList() : length(0), list(nullptr) {}

template <typename T>
CircularList<T>::~CircularList(){
  node<T> * ptr;
  if(list != nullptr){
    ptr = list->next;
    while(ptr != ptr->next){
      list->next = ptr->next;
      delete ptr;
      ptr = list->next;
    }
   delete ptr; 
  }
}

template <typename T>
int CircularList<T>::size(){
  return length;
}

template <typename T>
void CircularList<T>::add(T x){
  if(this->list == nullptr)
    addEmpty(x);
  else
    addNonEmpty(x);
  ++length;
}

template <typename T>
void CircularList<T>::merge(CircularList<T> * l){
	if(l->list != nullptr){
    if(this->list == nullptr){
      this->length = l->length;
      this->list = l->list;
    }
    else{
      node<T> * temp = this->list->next;
      this->list->next = l->list->next;   
      l->list->next = temp;
      this->length += l->length;
    }
    l->list = nullptr;
    l->length = 0;
  }
}

template <typename T>
node<T> * CircularList<T>::getList(){
  return list;
}

template <typename T>
node<T> * CircularList<T>::begin(){
  return list->next;
}

template <typename T>
node<T> * CircularList<T>::end(){
  return list;
}

template <typename T>
CircularList<T>::iterator::iterator(node<T> * n) : _it(n){};

template <typename T>
CircularList<T>::iterator::~iterator(){};

template <typename T>
typename CircularList<T>::iterator& CircularList<T>::iterator::operator++(){
  _it = _it->next;
  return *this;
}

template <typename T>
bool CircularList<T>::iterator:: operator ==(node<T> * n) const{
  return (_it == n);
}

template <typename T>
bool CircularList<T>::iterator:: operator !=(node<T> * n) const{
  return (_it != n);
}

template <typename T>
node<T>& CircularList<T>::iterator:: operator *(){
  return *_it;
}

template <typename T>
std::ostream & operator << (std::ostream & os, CircularList<T> & x){
	if(x.list != nullptr){
		auto it = x.begin();
		do {
			os << it->data << " ";
			it = it->next;
		} while(it != x.begin());
		os << std::endl;
	}
  return os;
}
