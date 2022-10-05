FROM fossa/haskell-static-alpine:ghc-8.10.7 as build

RUN mkdir /build && mkdir /dist
RUN git clone https://github.com/agda/agda.git /build/agda && cd /build/agda && git checkout efa6fe4cc
# Agda uses the data files feature of cabal, so we need to ensure that we copy those along with
# the binary. To do this, we just store everything in /dist, and copy over the whole directory.
#
# We also explicitly use v1-install because v2-install (which is just install on modern versions of cabal)
# just... ignores --datadir and --bindir? This would normally be a bad idea, but we are in a container
# so trashing the filesystem with a global build isn't an issue.
RUN cd /build/agda && cabal update && cabal v1-install alex happy && cabal v1-install --bindir=/dist --datadir=/dist --datasubdir=/dist/data --enable-executable-static
RUN git clone https://github.com/plt-amy/1lab /dist/1lab && cd /dist/1lab && git checkout f5465e94

FROM alpine:edge

# We need to install a handful of libraries,
# as GHC doesn't like statically linking against
# GMP.
RUN apk add --no-cache make gmp ncurses

COPY --from=build /dist /dist
COPY . ./build/agda-mugen

WORKDIR /build/agda-mugen
RUN make Everything.agda
RUN echo "/dist/1lab/1lab.agda-lib" > libraries
CMD ["/dist/agda", "-i=.", "--library-file=libraries", "src/Mugen/Everything.agda"]
