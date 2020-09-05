AGDA_FILES := $(shell find . -type f -and \( -path './src/*' -or -path './models/*' \) -and -name '*.agda')
AGDAI_FILES := $(subst .agda,.agdai,$(AGDA_FILES))
HTML_FILES := $(addsuffix .html,$(subst ./models/,./docs/,$(subst ./src/,./docs/,$(basename $(AGDA_FILES)))))
AGDA_MODULES := $(subst /,.,$(subst ./models/,,$(subst ./src/,,$(basename $(AGDA_FILES)))))


default: listings


########################
# Initialise Git hooks #
########################

.PHONY: init
init:
	git config core.hooksPath .githooks


#####################
# Typecheck library #
#####################

.PHONY: test
test: index.agda
	@echo "Checking amethyst..."
	@agda -i. -isrc -imodels index.agda


#####################
# Generate listings #
#####################

docs/index.html: index.agda
	@echo "Generating listings..."
	@agda -i. -isrc -imodels index.agda --html --html-dir=docs

.PHONY: listings
listings: $(HTML_FILES)

define HTML_template
$(1): docs/index.html
endef
$(foreach html_file,$(HTML_FILES),$(eval $(call HTML_template,$(html_file))))


#######################
# Generate index.agda #
#######################

INDEX_AGDA := "module index where\n\n"
$(foreach agda_module,$(AGDA_MODULES),$(eval INDEX_AGDA := $(INDEX_AGDA)"import $(agda_module)\n"))

index.agda: $(AGDA_FILES)
	@echo $(INDEX_AGDA) > index.agda


########################
# Install Dependencies #
########################

AGDA_REPO ?= https://github.com/agda/agda
AGDA_BRANCH ?= master
AGDA_COMMIT_HASH ?= 73405f70bced057d24dd4bf122d53f9548544aba

AGDA_STDLIB_REPO ?= https://github.com/agda/agda-stdlib
AGDA_STDLIB_BRANCH ?= experimental
AGDA_STDLIB_COMMIT_HASH ?= 3922be6a77cb925ac596010d882349aae1e45ff3

AGDARSEC_REPO ?= https://github.com/gallais/agdarsec
AGDARSEC_BRANCH ?= master
AGDARSEC_COMMIT_HASH ?= acd319c342c32dcb1fc5191091ae39ca07b3676e

SCHMITTY_REPO ?= https://github.com/wenkokke/schmitty
SCHMITTY_BRANCH ?= master
SCHMITTY_COMMIT_HASH ?= e35e9bbfa473be9aae41adf5ce845d5e1a2b2dbe

AGDA_CONF_DIR ?= $(HOME)/.agda
AGDA_LIBRARIES_FILE := $(AGDA_CONF_DIR)/libraries
AGDA_EXECUTABLES_FILE := $(AGDA_CONF_DIR)/executables

$(AGDA_LIBRARIES_FILE):
	mkdir -p $(AGDA_CONF_DIR)
	touch $(AGDA_LIBRARIES_FILE)

$(AGDA_EXECUTABLES_FILE):
	mkdir -p $(AGDA_CONF_DIR)
	touch $(AGDA_EXECUTABLES_FILE)

.PHONY: install-agda-source
install-agda-source:
ifndef AGDA_HOME
	@echo "Please set installation path using AGDA_HOME:\n"
	@echo "  AGDA_HOME=$HOME/agda make install-agda"
else
	git clone --single-branch --branch $(AGDA_BRANCH) $(AGDA_REPO) $(AGDA_HOME)
	cd $(AGDA_HOME) \
		&& git checkout $(AGDA_COMMIT_HASH) \
		&& git submodule update --init src/fix-whitespace
endif

.PHONY: install-agda-dependencies
install-agda-dependencies:
ifndef AGDA_HOME
	@echo "Please set installation path using AGDA_HOME:\n"
	@echo "  AGDA_HOME=$HOME/agda make install-agda"
else
	cd $(AGDA_HOME) \
		&& cabal v1-install --only-dependencies
endif

.PHONY: install-agda
install-agda:
ifndef AGDA_HOME
	@echo "Please set installation path using AGDA_HOME:\n"
	@echo "  AGDA_HOME=$HOME/agda make install-agda"
else
	cd $(AGDA_HOME) \
		&& cabal v1-install \
			--disable-documentation \
			--disable-library-profiling \
			-fenable-cluster-counting \
			--ghc-options="+RTS -M4G -RTS"
endif

.PHONY: install-agda-stdlib
install-agda-stdlib: $(AGDA_LIBRARIES_FILE)
ifndef AGDA_STDLIB_HOME
	@echo "Please set installation path using AGDA_STDLIB_HOME:\n"
	@echo "  AGDA_STDLIB_HOME=$HOME/agda make install-agda-stdlib"
else
	git clone --single-branch --branch $(AGDA_STDLIB_BRANCH) $(AGDA_STDLIB_REPO) $(AGDA_STDLIB_HOME)
	cd $(AGDA_STDLIB_HOME) && git checkout $(AGDA_STDLIB_COMMIT_HASH)
ifeq (,$(findstring $(AGDA_STDLIB_HOME),$(shell cat $(AGDA_LIBRARIES_FILE))))
	@echo $(AGDA_STDLIB_HOME)/standard-library.agda-lib >> $(AGDA_LIBRARIES_FILE)
endif
endif

.PHONY: install-agdarsec
install-agdarsec: $(AGDA_LIBRARIES_FILE)
ifndef AGDARSEC_HOME
	@echo "Please set installation path using AGDARSEC_HOME:\n"
	@echo "  AGDARSEC_HOME=$HOME/agda make install-agdarsec"
else
	git clone --single-branch --branch $(AGDARSEC_BRANCH) $(AGDARSEC_REPO) $(AGDARSEC_HOME)
	cd $(AGDARSEC_HOME) && git checkout $(AGDARSEC_COMMIT_HASH)
ifeq (,$(findstring $(AGDARSEC_HOME),$(shell cat $(AGDA_LIBRARIES_FILE))))
	@echo $(AGDARSEC_HOME)/agdarsec.agda-lib >> $(AGDA_LIBRARIES_FILE)
endif
endif

.PHONY: install-schmitty
install-schmitty: $(AGDA_LIBRARIES_FILE)
ifndef SCHMITTY_HOME
	@echo "Please set installation path using SCHMITTY_HOME:\n"
	@echo "  SCHMITTY_HOME=$HOME/agda make install-schmitty"
else
	git clone --single-branch --branch $(SCHMITTY_BRANCH) $(SCHMITTY_REPO) $(SCHMITTY_HOME)
	cd $(SCHMITTY_HOME) && git checkout $(SCHMITTY_COMMIT_HASH)
ifeq (,$(findstring $(SCHMITTY_HOME),$(shell cat $(AGDA_LIBRARIES_FILE))))
	@echo $(SCHMITTY_HOME)/schmitty.agda-lib >> $(AGDA_LIBRARIES_FILE)
endif
endif

.PHONY: register-z3
register-z3: $(AGDA_EXECUTABLES_FILE)
ifeq (,$(findstring z3,$(shell cat $(AGDA_EXECUTABLES_FILE))))
	@echo $(shell which z3) >> $(AGDA_EXECUTABLES_FILE)
endif

.PHONY: register-cvc4
register-cvc4: $(AGDA_EXECUTABLES_FILE)
ifeq (,$(findstring cvc4,$(shell cat $(AGDA_EXECUTABLES_FILE))))
	@echo $(shell which cvc4) >> $(AGDA_EXECUTABLES_FILE)
endif
