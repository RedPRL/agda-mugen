FROM haskell:8.10.7

LABEL "com.github.actions.name"="Check Agda-Mugen"
LABEL "com.github.actions.description"="Typechecks the Agda-Mugen project"

RUN mkdir /build/
RUN git clone https://github.com/agda/agda.git /build/agda && cd /build/agda && git checkout efa6fe4cc
RUN cd agda && cabal update && cabal install
RUN git clone https://github.com/plt-amy/1lab /build/1lab && cd /build/1lab && git checkout f5465e94
COPY . ./agda-mugen

RUN echo "/build/1lab/1lab.agda-lib" > libraries

ADD *.sh /

ENTRYPOINT ["/entrypoint.sh"]