.PHONY: test Everything.agda clean

RTSARGS = +RTS -H6G -A64M -RTS

test: Everything.agda
	agda ${RTSARGS} Everything.agda

Everything.agda:
	find . -name '[^\.]*.agda' | sed -e 's|^./|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' | sort > Everything.agda

clean:
	find . -name '*.agdai' -exec rm \{\} \;
