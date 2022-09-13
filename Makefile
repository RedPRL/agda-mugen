.PHONY: Everything.agda build

Everything.agda:
	find ./src -name "*.agda" | sed -e 's|^./src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Mugen.Everything/d' | LC_COLLATE='C' sort > ./src/Mugen/Everything.agda

build: Everything.agda
	agda -i=. ./src/Mugen/Everything.agda
