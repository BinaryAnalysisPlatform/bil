LATEX = pdflatex

OTT_FLAGS = -tex_wrap false -coq_lngen true

all : bil.pdf coq

coq: bil.ott Makefile
	ott $(OTT_FLAGS) bil.ott -o bil.v

bil.pdf : bil.ott bil.tex Makefile
	ott $(OTT_FLAGS) bil.ott -o ott.tex -tex_filter bil.tex bil_filtered.tex
	$(LATEX) bil_filtered.tex
	$(LATEX) bil_filtered.tex
	mv bil_filtered.pdf bil.pdf

clean :
	rm -f ott.tex bil.pdf bil_filtered.tex *.log *.toc *.aux
