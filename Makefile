.PHONY: test src/Everything.agda clean

OTHEROPTS=

RTSARGS = +RTS -M6G ${OTHEROPTS} -RTS

test: src/Everything.agda
	agda ${RTSARGS} -isrc src/Everything.agda

html: src/Everything.agda
	agda ${RTSARGS} --html -isrc src/Everything.agda

src/Everything.agda:
	find src/ -name '[^\.]*.agda' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' | LC_COLLATE='C' sort > src/Everything.agda

clean:
	find . -name '*.agdai' -exec rm \{\} \;

profile: src/Everything.agda
	agda ${RTSARGS} -v profile:7 -v profile.modules:15 -v profile.definitions:15 src/Everything.agda
