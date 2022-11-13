####################################################################################################
# Stage 1: building everything except agda-mugen
####################################################################################################

FROM fossa/haskell-static-alpine:ghc-8.10.7 AS agda

WORKDIR /build/agda
RUN \
  git init && \
  git remote add origin https://github.com/agda/agda.git && \
  git fetch --depth 1 origin efa6fe4cc65132bcc375f608542154674a37f1ba && \
  git checkout FETCH_HEAD

# We build Agda and place it in /dist along with its data files.
# We explicitly use v1-install because v2-install does not support --datadir and --bindir
# to relocate executables and data files yet.
RUN \
  mkdir -p /dist && \
  cabal update && \
  cabal v1-install alex happy && \
  cabal v1-install --bindir=/dist --datadir=/dist --datasubdir=/dist/data --enable-executable-static

####################################################################################################
# Stage 2: Agda and 1lab (everything except agda-mugan)
####################################################################################################

FROM alpine:edge AS ci

# We need gmp and ncurses because GHC doesn't statically link agda against GMP.
# We also need git to check out 1lab.
RUN apk add --no-cache gmp ncurses git

COPY --from=agda /dist /dist

WORKDIR /dist/1lab
RUN \
  git init && \
  git remote add origin https://github.com/plt-amy/1lab && \
  git fetch --depth 1 origin f5465e947501f971bd2dfb76915e4065b13194c5 && \
  git checkout FETCH_HEAD
RUN echo "/dist/1lab/1lab.agda-lib" > /dist/libraries

###############################################################################################################

FROM alpine:edge

COPY --from=ci /dist /dist

WORKDIR /build/agda-mugen
COPY ["src", "/build/agda-mugen/src"]
COPY ["Makefile", "/build/agda-mugen/Makefile"]
COPY ["agda-mugen.agda-lib", "/build/agda-mugen/agda-mugen.agda-lib"]

CMD ["/dist/agda", "-i=.", "--library-file=/dist/libraries", "src/Mugen/Everything.agda"]
