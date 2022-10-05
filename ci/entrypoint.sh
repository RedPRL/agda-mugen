#! /bin/sh

make Everything.agda
/dist/agda -i=. --library-file=libraries src/Mugen/Everything.agda
