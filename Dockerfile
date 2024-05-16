####################################################################################################
# Stage 1: building everything except agda-mugen
####################################################################################################

ARG GHC_VERSION=9.4.7
FROM fossa/haskell-static-alpine:ghc-${GHC_VERSION} AS agda

WORKDIR /build/agda
ARG AGDA_VERSION=403ee4263e0f14222956e398d2610ae1a4f05467
RUN \
  git init && \
  git remote add origin https://github.com/agda/agda.git && \
  git fetch --depth 1 origin "${AGDA_VERSION}" && \
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
# Stage 2: Download 1lab (everything except agda-mugan)
####################################################################################################

FROM alpine AS onelab

RUN apk add --no-cache git

WORKDIR /dist/1lab
ARG ONELAB_VERSION=caf71247aa81493629cb89767e19103647ace0f2
RUN \
  git init && \
  git remote add origin https://github.com/plt-amy/1lab && \
  git fetch --depth 1 origin "${ONELAB_VERSION}" && \
  git checkout FETCH_HEAD
RUN echo "/dist/1lab/1lab.agda-lib" > /dist/libraries

###############################################################################################################

FROM scratch

COPY --from=agda /dist /dist
COPY --from=onelab /dist /dist

WORKDIR /build/agda-mugen
COPY ["src", "/build/agda-mugen/src"]
COPY ["Makefile", "/build/agda-mugen/Makefile"]
COPY ["agda-mugen.agda-lib", "/build/agda-mugen/agda-mugen.agda-lib"]

CMD ["/dist/agda", "-i=.", "--library-file=/dist/libraries", "src/Mugen/Everything.agda"]
