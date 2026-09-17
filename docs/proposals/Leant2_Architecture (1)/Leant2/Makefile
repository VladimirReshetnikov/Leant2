.PHONY: pdf behavior lean clean

pdf:
	cd article && xelatex -interaction=nonstopmode -halt-on-error Leant2.tex
	cd article && xelatex -interaction=nonstopmode -halt-on-error Leant2.tex
	cd article && xelatex -interaction=nonstopmode -halt-on-error Leant2.tex

behavior:
	python3 experiments/behavior_lab.py

lean:
	cd prototype && lean NativeCore.lean
	cd prototype && lean Certificates.lean

clean:
	rm -f article/Leant2.aux article/Leant2.log article/Leant2.out article/Leant2.toc
