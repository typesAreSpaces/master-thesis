(TeX-add-style-hook
 "main"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("acmart" "sigconf" "authordraft")))
   (TeX-run-style-hooks
    "latex2e"
    "acmart"
    "acmart10"
    "algpseudocode"
    "algorithm")
   (TeX-add-symbols
    "BibTeX")
   (LaTeX-add-labels
    "aha")
   (LaTeX-add-bibliographies
    "references"))
 :latex)

