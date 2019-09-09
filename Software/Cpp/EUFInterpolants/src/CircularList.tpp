template <typename T>
CircularList<T>::CircularList() : length(0), elements(nullptr) {}

template <typename T>
CircularList<T>::~CircularList(){
  node<T> * curr_ptr;
  if(!this->empty()){
    this->length = 0;
    curr_ptr = elements->next;
    while(curr_ptr != curr_ptr->next){
      elements->next = curr_ptr->next;
      delete curr_ptr;
      curr_ptr = elements->next;
    }
    delete curr_ptr;
  }
}

template <typename T>
unsigned int CircularList<T>::size(){
  return length;
}

template <typename T>
void CircularList<T>::add(const T & element){
  if(this->empty())
    addEmpty(element);
  else
    addNonEmpty(element);
  ++length;
}

template <typename T>
void CircularList<T>::addEmpty(const T & element){
  node<T> * new_elements = new node<T>;
  new_elements->data = element;
  new_elements->next = new_elements;
  elements = new_elements;
}

template <typename T>
void CircularList<T>::addNonEmpty(const T & element){
  node<T> * new_elements = new node<T>;
  new_elements->data = element;
  new_elements->next = elements->next;
  elements->next = new_elements;
  elements = new_elements;
}

template <typename T>
void CircularList<T>::merge(CircularList<T> & circular_list){
  if(!circular_list.empty()){
    if(this->empty()){
      this->length = circular_list.length;
      this->elements = circular_list.elements;
    }
    else{
      node<T> * new_elements = this->elements->next;
      this->elements->next = circular_list.elements->next;
      circular_list.elements->next = new_elements;
      this->length += circular_list.length;
    }
    circular_list.elements = nullptr;
    circular_list.length = 0;
  }
}

template <typename T>
const node<T> & CircularList<T>::getElements(){
  return elements;
}

template <typename T>
node<T> * CircularList<T>::begin(){
  return elements->next;
}

template <typename T>
node<T> * CircularList<T>::end(){
  return elements;
}

template <typename T>
bool CircularList<T>::empty(){
  return (this->elements == nullptr);
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
std::ostream & operator << (std::ostream & os, CircularList<T> & x){;
  if(!x.empty()){
    auto it = x.begin();
    do {
      os << (it->data) << " ";
      it = it->next;
    } while(it != x.begin());
  }
  return os;
}

// Use only with CircularList<Term*>, for the moment
template <typename T>
std::ostream & operator << (std::ostream & os, CircularList<T*> & x){
  if(!x.empty()){
    auto it = x.begin();
    do {
      os << (it->data)->getId() << " ";
      it = it->next;
    } while(it != x.begin());
  }
  return os;
}
