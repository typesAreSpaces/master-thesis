class Hornsat;

class CongruenceClosureExplain : public CongruenceClosure {

  Hornsat * hsat;

  PendingElements pending_elements;
  PendingPointers equations_to_merge;
  PendingPointers pending_to_propagate;

  FactoryCurryNodes const & factory_curry_nodes;

  LookupTable lookup_table;
  UseList     use_list;

  void pushPending(PendingPointers &, const PendingElement &);
  void merge();
  void merge(EquationCurryNodes const &);
  void propagate();
  void propagateAux(CurryNode const &, CurryNode const &, EqClass, EqClass, PendingElement const &);

  EqClass         highestNode(EqClass, UnionFind &);
  EqClass         nearestCommonAncestor(EqClass, EqClass, UnionFind &);
  PendingPointers explain(EqClass, EqClass);
  void            explainAlongPath(EqClass, EqClass, UnionFind &, ExplainEquations &, PendingPointers &);
  std::ostream &  giveExplanation(std::ostream &, EqClass, EqClass);

  public:
  CongruenceClosureExplain(Hornsat *, CongruenceClosureExplain const &, UnionFindExplain &);
  CongruenceClosureExplain(Z3Subterms const &, UnionFindExplain &, FactoryCurryNodes &, IdsToMerge const &);
  ~CongruenceClosureExplain();

  bool areSameClass(EqClass, EqClass);
  bool areSameClass(z3::expr const &, z3::expr const &);
  
  EqClass  constantId(EqClass);
  EqClass  find(EqClass);
  z3::expr z3Repr(z3::expr const &);

  void merge(EqClass, EqClass);
  void merge(z3::expr const &, z3::expr const &);

  PendingPointers explain(z3::expr const &, z3::expr const &);
  std::ostream &  giveExplanation(std::ostream &, z3::expr const &, z3::expr const &);

  z3::expr_vector z3Explain(z3::expr const &, z3::expr const &);
  std::ostream &  z3Explanation(std::ostream &, const z3::expr &, const z3::expr &);

  friend std::ostream & operator << (std::ostream &, const CongruenceClosureExplain &);
};

