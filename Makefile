OTT ?= opam exec --switch=5.5.2+frama-c -- ott

hol/tracesScript.sml: ott/traces.ott
	cd hol && $(OTT) -i ../ott/traces.ott -o tracesScript.sml

ott/traces.pdf: ott/traces.ott
	cd ott && $(OTT) -i traces.ott -o traces.tex && pdflatex -interaction=nonstopmode traces.tex

build: hol/tracesScript.sml
	holbuild build

.PHONY: build
