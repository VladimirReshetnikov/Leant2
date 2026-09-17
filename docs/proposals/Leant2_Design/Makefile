.PHONY: article lean reference clean
article:
	cd article && latexmk -pdf -interaction=nonstopmode -halt-on-error Leant2.tex
lean:
	./scripts/check_local.sh
reference:
	python3 scripts/finite_reference.py
clean:
	cd article && latexmk -c
