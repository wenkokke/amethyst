FROM ubuntu:20.04

# Copy amethyst
COPY . /amethyst

# Set the working directory.
USER root
ENV HOME /root
WORKDIR /amethyst

# Setup common tools
ENV DEBIAN_FRONTEND noninteractive
ENV TZ Europe/London
ENV LANG C.UTF-8
RUN apt-get update -y
RUN apt-get install -y git make tzdata

# Setup Z3, CVC4, etc...
RUN apt-get install -y z3 cvc4
RUN make register-z3 register-cvc4

# Setup Haskell
RUN apt-get install -y ghc cabal-install
RUN cabal v1-update
RUN cabal v1-install alex happy
ENV PATH ${PATH}:${HOME}/.cabal/bin

# Setup Agda
ENV AGDA_HOME /agda
RUN apt-get install -y zlib1g-dev libicu-dev
RUN make install-agda-source
RUN make install-agda-dependencies
RUN make install-agda

# Setup agda-stdlib
ENV AGDA_STDLIB_HOME /agda-stdlib
RUN make install-agda-stdlib

# Setup agdarsec
ENV AGDARSEC_HOME /agdarsec
RUN make install-agdarsec

# Setup schmitty
ENV SCHMITTY_HOME /schmitty
RUN make install-schmitty

# Test amethyst
CMD make test
