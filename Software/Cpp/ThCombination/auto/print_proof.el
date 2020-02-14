(TeX-add-style-hook
 "print_proof"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("standalone" "varwidth=2000pt")))
   (TeX-run-style-hooks
    "latex2e"
    "standalone"
    "standalone10"
    "ebproof"
    "amssymb"
    "amsmath"
    "xcolor"))
 :latex)

