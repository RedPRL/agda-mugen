.PHONY: Everything.agda build clean

build: Everything.agda
	agda -i=. ./src/Mugen/Everything.agda

Everything.agda:
	echo "module Mugen.Everything where" > ./src/Mugen/Everything.agda
	find ./src -name "*.agda" | sed -e 's|^./src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Mugen.Everything/d' | LC_COLLATE='C' sort >> ./src/Mugen/Everything.agda

clean:
	rm ./src/Mugen/Everything.agda
