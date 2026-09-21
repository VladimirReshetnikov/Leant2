LATEXMK ?= latexmk
PYTHON ?= python3

.PHONY: all check clean

all: article.pdf model_checks.json

article.pdf: article.tex
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

model_checks.json: model_checks.py
	$(PYTHON) model_checks.py --output $@

check:
	$(PYTHON) model_checks.py --output model_checks.json
	$(PYTHON) -m py_compile model_checks.py

clean:
	$(LATEXMK) -c article.tex
