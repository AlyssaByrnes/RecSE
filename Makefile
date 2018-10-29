ifeq ($(OS), Windows_NT)
	RM := del /F
else
	RM := rm -f
endif

.PHONY: clean

LATEX=latex -shell-escape
BIBTEX=bibtex
DVIPS=dvips
PS2PDF=ps2pdf
SOURCES=RecSEPaper.tex
EXE=RecSEPaper

all: $(EXE)

$(EXE): $(SOURCES)
	$(LATEX)  $@
	$(BIBTEX) $@
	$(LATEX)  $@
	$(LATEX)  $@
	$(DVIPS) -P cmz $@.dvi -o $@.ps -t letter
	$(PS2PDF) $@.ps $@.pdf

clean:
	$(RM) *.out *.log *.pbm *.ps *.pdf *.dvi *.bbl *.blg *.aux
