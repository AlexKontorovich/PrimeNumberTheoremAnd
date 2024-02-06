all:
	plastex -c plastex.cfg web.tex

pdf:
	mkdir -p print
	xelatex -output-directory=print print.tex

clean-aux:
	rm -f blueprint.paux

clean: clean-aux
	rm -rf web

