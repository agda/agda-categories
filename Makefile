.PHONY: test Everything.agda clean

AGDA_EXEC = agda
OTHEROPTS = -Werror
RTSARGS = +RTS -M6G -A128M -RTS
AGDA=$(AGDA_EXEC) $(OTHEROPTS) $(RTSARGS)

test: Everything.agda
	$(AGDA) -i. Everything.agda

html: Everything.agda
	$(AGDA) --html -i. Everything.agda

Everything.agda:
	git ls-tree --full-tree -r --name-only HEAD | grep '^src/[^\.]*.agda' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' | LC_COLLATE='C' sort > Everything.agda

clean:
	find . -name '*.agdai' -exec rm \{\} \;

profile: Everything.agda
	$(AGDA) -v profile:7 -v profile.definitions:15 -i. Everything.agda
