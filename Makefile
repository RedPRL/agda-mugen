.PHONY: Everything.agda build package

Everything.agda:
	find ./src -name "*.agda" | sed -e 's|^./src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' | LC_COLLATE='C' sort > ./src/Everything.agda

build: Everything.agda
	agda -i=. ./src/Everything.agda
