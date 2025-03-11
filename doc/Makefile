all: clean report.pdf

%.pdf: %.md
	@pandoc --number-sections $< -o $@ --pdf-engine=xelatex --standalone --listings --from=markdown+escaped_line_breaks

clean: 
	@rm -f *.pdf

.PHONY: all
