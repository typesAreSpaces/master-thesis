(TeX-add-style-hook
 "sample-authordraft"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("acmart" "sigconf" "authordraft")))
   (TeX-run-style-hooks
    "latex2e"
    "acmart"
    "acmart10")
   (TeX-add-symbols
    "BibTeX")
   (LaTeX-add-bibliographies
    "sample-base"))
 :latex)

