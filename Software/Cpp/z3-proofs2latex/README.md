# z3-proofs2latex

A small script to produce a natural derivation using a z3 proof produced by the C++/Python API.

Edit the path file in either proof_unsat.py or proof_unsat.cpp to parse the smt formula.

Obtain the pdf file proof_python.pdf using
```
    $ make proof_python
```

Obtain the pdf file proof_cpp.pdf using
```
    $ make proof_cpp
```

There is an issue with the varwidth in the implementation using the proof from the Cpp api. The system doesn't automatically detect the optimal varwith. You can change, if needed, this variable by changing _varwidth in z3-proof-parser-sexpr.y

Currently, it supports the logic "QF_UFLIA".
