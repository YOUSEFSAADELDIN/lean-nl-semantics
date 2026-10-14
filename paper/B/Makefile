# Builds main.pdf. The ACL style files are fetched from their official
# repository (pinned commit) rather than copied here.
ACL_STYLE_REPO = https://github.com/acl-org/acl-style-files
ACL_STYLE_COMMIT = d5adc823ff0f80f98c80405ca0ab66c68e684409

main.pdf: main.tex references.bib acl.sty acl_natbib.bst
	pdflatex -interaction=nonstopmode main
	bibtex main
	pdflatex -interaction=nonstopmode main
	pdflatex -interaction=nonstopmode main

acl.sty acl_natbib.bst:
	rm -rf .acl-style-files
	git clone --quiet $(ACL_STYLE_REPO) .acl-style-files
	git -C .acl-style-files checkout --quiet $(ACL_STYLE_COMMIT)
	cp .acl-style-files/acl.sty .acl-style-files/acl_natbib.bst .
	rm -rf .acl-style-files

clean:
	rm -f main.aux main.bbl main.blg main.log main.out main.pdf

.PHONY: clean
