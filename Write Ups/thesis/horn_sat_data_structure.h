class Hornsat {

  friend class EUFInterpolant;

  unsigned num_hcs, num_literals;
  // This structure is only used in our approach
  // for conditional-elimination
  std::unordered_map<unsigned, HornClause *> head_term_indexer;

  UnionFindExplain         ufe;
  CongruenceClosureExplain equiv_classes;

  std::vector<Literal>   list_of_literals;
  ClassList              class_list;
  std::vector<unsigned>  num_args;
  std::vector<LiteralId> pos_lit_list;
  // 'facts' is a queue of all the (temporary)
  // literals that have value true
  std::queue<LiteralId>  facts;
  std::queue<TermIdPair> to_combine;

  bool consistent;

  void satisfiable();
  void closure();
  
 public:
  Hornsat(CongruenceClosureExplain &, HornClauses const &);
  ~Hornsat();

  void build(CongruenceClosureExplain &, HornClauses const &);
  bool isConsistent() const ;
  void unionupdate(LiteralId, LiteralId);
  friend std::ostream & operator << (std::ostream &, Hornsat const &);
};
