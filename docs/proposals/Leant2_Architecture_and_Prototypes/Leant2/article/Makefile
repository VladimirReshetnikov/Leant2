.PHONY: all clean
all: leant2.pdf
leant2.pdf: leant2.tex references.tex $(wildcard sections/*.tex) ../prototype/Core.lean ../prototype/Behavior.lean
	pdflatex -interaction=nonstopmode -halt-on-error leant2.tex
	pdflatex -interaction=nonstopmode -halt-on-error leant2.tex
	pdflatex -interaction=nonstopmode -halt-on-error leant2.tex
clean:
	rm -f leant2.aux leant2.log leant2.out leant2.toc
