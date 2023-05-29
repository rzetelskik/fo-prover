all: build

DIR := $(shell pwd)
CABAL_BIN ?= $(shell which cabal)
CABAL_INSTALL_OPTS ?= --install-method=copy --installdir=$(DIR) --overwrite-policy=always

build: 
	$(CABAL_BIN) install $(CABAL_INSTALL_OPTS)
.PHONY: build

clean:
	$(CABAL_BIN) clean
	rm FO-prover
.PHONY: clean