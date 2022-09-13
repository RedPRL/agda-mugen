FROM haskell:8.10.7

WORKDIR /build/

RUN git clone https://github.com/agda/agda.git && cd agda && git checkout efa6fe4cc
RUN cd agda && cabal update && cabal install
RUN git clone https://github.com/plt-amy/1lab && cd 1lab && git checkout f5465e94
COPY . ./agda-mugen

WORKDIR /build/agda-mugen
RUN make Everything.agda
RUN echo "/build/1lab/1lab.agda-lib" > libraries
CMD ["agda", "-i=.", "--library-file=libraries", "src/Everything.agda"]