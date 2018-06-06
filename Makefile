LATEX = pdflatex

OTT_FLAGS = -tex_wrap false -coq_lngen true

COQFLAGS= -Q ../bbv bbv  -Q . bil
DEPFLAGS:=$(COQFLAGS)

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc


all : bil.pdf Sized_Word.vo bil.vo

bil.v: bil.ott Makefile
	ott $(OTT_FLAGS) bil.ott -o bil.v

bil.pdf : bil.ott bil.tex Makefile
	ott $(OTT_FLAGS) bil.ott -o ott.tex -tex_filter bil.tex bil_filtered.tex
	$(LATEX) bil_filtered.tex
	$(LATEX) bil_filtered.tex
	mv bil_filtered.pdf bil.pdf


%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v


clean :
	rm -f ott.tex bil.pdf bil_filtered.tex *.log *.toc *.aux *.vo bil.v
