OTT ?= opam exec --switch=5.5.2+ott -- ott

hol/tracesScript.sml: ott/traces.ott
	cd hol && $(OTT) -i ../ott/traces.ott -o tracesScript.sml

ott/traces.pdf: ott/traces.ott
	cd ott && $(OTT) -i traces.ott -o traces.tex && pdflatex -interaction=nonstopmode traces.tex

doc/ott-rules.tex: ott/traces.ott
	cd doc && $(OTT) -i ../ott/traces.ott -o ott-rules.tex -tex_wrap false -tex_name_prefix ott

doc/note.pdf: doc/note.tex doc/ott-rules.tex
	cd doc && pdflatex -interaction=nonstopmode note.tex && pdflatex -interaction=nonstopmode note.tex

doc/verif.pdf: doc/verif.tex
	cd doc && pdflatex -interaction=nonstopmode verif.tex && pdflatex -interaction=nonstopmode verif.tex

doc/fol.pdf: doc/fol.tex
	cd doc && pdflatex -interaction=nonstopmode fol.tex && pdflatex -interaction=nonstopmode fol.tex

build: hol/tracesScript.sml
	holbuild build

.PHONY: build
