(TeX-add-style-hook
 "main"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("acmart" "10pt" "sigconf" "authordraft")))
   (TeX-run-style-hooks
    "latex2e"
    "acmart"
    "acmart10"
    "algpseudocode"
    "algorithm"
    "setspace")
   (TeX-add-symbols
    "BibTeX")
   (LaTeX-add-labels
    "aha")
   (LaTeX-add-bibliographies
    "references"))
 :latex)

