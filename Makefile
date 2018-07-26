
LATEX = pdflatex

OTT_FLAGS = -tex_wrap false -coq_lngen true

COQFLAGS= -Q ../bbv bbv  -Q . bil
DEPFLAGS:=$(COQFLAGS)

COQC=$(COQBIN)coqc
COQTOP=$(COQBIN)coqtop
COQDEP=$(COQBIN)coqdep $(DEPFLAGS)
COQDOC=$(COQBIN)coqdoc

EXPECTED_BBV_VERSION=08ab43a873f1cb574515589cfa2c56a9aa9bd023
ACTUAL_BBV_VERSION=$(shell cd ../bbv && git rev-parse HEAD)

ifneq ($(EXPECTED_BBV_VERSION),$(ACTUAL_BBV_VERSION))
  $(error bbv library not in adjacent directory or of the wrong version.\
HEAD should be $(EXPECTED_BBV_VERSION) but was $(ACTUAL_BBV_VERSION).\
Make sure that you have the correct version from "https://github.com/mit-plv/bbv")
endif


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
