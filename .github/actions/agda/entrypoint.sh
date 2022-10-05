#! /bin/sh

make Everything.agda
agda -i=. --library-file=/build/libraries src/Mugen/Everything.agda
