.PHONY: test Everything.agda

test: Everything.agda
	agda Everything.agda

Everything.agda:
	find . -name '[^\.]*.agda' | sed -e 's|^./|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' | sort > Everything.agda
