LATEX = pdflatex

OTT_FLAGS = -tex_wrap false

all : bil.pdf

bil.pdf : bil.ott bil.tex Makefile
	ott $(OTT_FLAGS) bil.ott -o ott.tex
	$(LATEX) bil.tex
	$(LATEX) bil.tex

clean :
	rm -f ott.tex bil.aux bil.pdf bil.log bil.toc bil.pdf ott.aux
