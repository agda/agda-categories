.PHONY: test Everything.agda clean

OTHEROPTS = --auto-inline -Werror

RTSARGS = +RTS -M6G -A128M -RTS ${OTHEROPTS}

test: Everything.agda
	agda ${RTSARGS} -i. Everything.agda

html: Everything.agda
	agda ${RTSARGS} --html -i. Everything.agda

Everything.agda:
	git ls-tree --full-tree -r --name-only HEAD | grep '^src/[^\.]*.agda' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' | LC_COLLATE='C' sort > Everything.agda

clean:
	find . -name '*.agdai' -exec rm \{\} \;

profile: Everything.agda
	agda ${RTSARGS} -v profile:7 -v profile.definitions:15 -i. Everything.agda
