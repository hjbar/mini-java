all: report.pdf

%.pdf: %.md
	pandoc --number-sections $< -o $@ --pdf-engine=xelatex

.PHONY: all
