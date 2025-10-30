.PHONY: all pdf figs tables clean

all: pdf figs tables

pdf:
	cd docs && latexmk -pdf -shell-escape formal_manuscript.tex

figs:
	@echo "Generating figures..."
	@if [ -f scripts/make_figs.py ]; then python3 scripts/make_figs.py; else echo "scripts/make_figs.py not found, skipping"; fi

tables:
	@echo "Generating tables..."
	@if [ -f scripts/make_tables.py ]; then python3 scripts/make_tables.py; else echo "scripts/make_tables.py not found, skipping"; fi

clean:
	cd docs && latexmk -C
	rm -f docs/*.aux docs/*.bbl docs/*.bcf docs/*.blg docs/*.log docs/*.out docs/*.run.xml docs/*.toc

help:
	@echo "Available targets:"
	@echo "  all      - Build PDF, figures, and tables"
	@echo "  pdf      - Build the PDF document"
	@echo "  figs     - Generate figures"
	@echo "  tables   - Generate tables"
	@echo "  clean    - Remove generated files"
	@echo "  help     - Show this help message"
