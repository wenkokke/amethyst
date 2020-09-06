AGDA_FILES := $(shell find . -type f -and \( -path './src/*' -or -path './models/*' \) -and -name '*.agda')
AGDAI_FILES := $(subst .agda,.agdai,$(AGDA_FILES))
HTML_FILES := $(addsuffix .html,$(subst ./models/,./docs/,$(subst ./src/,./docs/,$(basename $(AGDA_FILES)))))
AGDA_MODULES := $(subst /,.,$(subst ./models/,,$(subst ./src/,,$(basename $(AGDA_FILES)))))

AGDA ?= agda


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
	$(AGDA) -i. -isrc -imodels index.agda


#####################
# Generate listings #
#####################

docs/index.html: index.agda
	@echo "Generating listings..."
	$(AGDA) -i. -isrc -imodels index.agda --html --html-dir=docs

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

AGDA_DIR ?= $(HOME)/.agda
AGDA_LIBRARIES_FILE := $(AGDA_DIR)/libraries
AGDA_EXECUTABLES_FILE := $(AGDA_DIR)/executables

AGDA_REPO ?= https://github.com/agda/agda
AGDA_PR ?= 4885
AGDA_BRANCH ?= master
AGDA_COMMIT_HASH ?= HEAD

AGDA_STDLIB_HOME ?= $(AGDA_DIR)/standard-library
AGDA_STDLIB_REPO ?= https://github.com/agda/agda-stdlib
AGDA_STDLIB_PR ?= 1285
AGDA_STDLIB_BRANCH ?= experimental
AGDA_STDLIB_COMMIT_HASH ?= HEAD

AGDARSEC_HOME ?= $(AGDA_DIR)/agdarsec
AGDARSEC_REPO ?= https://github.com/gallais/agdarsec
AGDARSEC_PR ?= 17
AGDARSEC_BRANCH ?= master
AGDARSEC_COMMIT_HASH ?= HEAD

SCHMITTY_HOME ?= $(AGDA_DIR)/schmitty
SCHMITTY_REPO ?= https://github.com/wenkokke/schmitty
SCHMITTY_BRANCH ?= master
SCHMITTY_COMMIT_HASH ?= HEAD

$(AGDA_LIBRARIES_FILE):
	mkdir -p $(AGDA_DIR)
	touch $(AGDA_LIBRARIES_FILE)

$(AGDA_EXECUTABLES_FILE):
	mkdir -p $(AGDA_DIR)
	touch $(AGDA_EXECUTABLES_FILE)

.PHONY: install-agda-source
install-agda-source:
ifndef AGDA_HOME
	@echo "Please set installation path using AGDA_HOME:\n"
	@echo "  AGDA_HOME=$HOME/agda make install-agda"
else
ifneq ($(dirname $(AGDA_HOME)),)
	if [ ! -d "$(dirname $(AGDA_HOME))" ]; then mkdir -p $(dirname $(AGDA_HOME)); fi
endif
ifdef AGDA_PR
	git clone $(AGDA_REPO) $(AGDA_HOME)
	cd $(AGDA_HOME) \
		&& git fetch origin pull/$(AGDA_PR)/head:pull-$(AGDA_PR) \
		&& git checkout pull-$(AGDA_PR)
else
	git clone --single-branch --branch $(AGDA_BRANCH) $(AGDA_REPO) $(AGDA_HOME)
	cd $(AGDA_HOME) \
		&& git checkout $(AGDA_COMMIT_HASH)
endif
	cd $(AGDA_HOME) \
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
	@echo "  AGDA_STDLIB_HOME=\$HOME/agda make install-agda-stdlib"
else
ifneq ($(dirname $(AGDA_STDLIB_HOME)),)
	if [ ! -d "$(dirname $(AGDA_STDLIB_HOME))" ]; then mkdir -p $(dirname $(AGDA_STDLIB_HOME)); fi
endif
ifdef AGDA_STDLIB_PR
	git clone $(AGDA_STDLIB_REPO) $(AGDA_STDLIB_HOME)
	cd $(AGDA_STDLIB_HOME) \
		&& git fetch origin pull/$(AGDA_STDLIB_PR)/head:pull-$(AGDA_STDLIB_PR) \
		&& git checkout pull-$(AGDA_STDLIB_PR)
else
	git clone --single-branch --branch $(AGDA_STDLIB_BRANCH) $(AGDA_STDLIB_REPO) $(AGDA_STDLIB_HOME)
	cd $(AGDA_STDLIB_HOME) && git checkout $(AGDA_STDLIB_COMMIT_HASH)
ifeq (,$(findstring $(AGDA_STDLIB_HOME),$(shell cat $(AGDA_LIBRARIES_FILE))))
	@echo $(AGDA_STDLIB_HOME)/standard-library.agda-lib >> $(AGDA_LIBRARIES_FILE)
endif
endif
endif

.PHONY: install-agdarsec
install-agdarsec: $(AGDA_LIBRARIES_FILE)
ifndef AGDARSEC_HOME
	@echo "Please set installation path using AGDARSEC_HOME:\n"
	@echo "  AGDARSEC_HOME=\$HOME/agda make install-agdarsec"
else
ifneq ($(dirname $(AGDARSEC_HOME)),)
	if [ ! -d "$(dirname $(AGDARSEC_HOME))" ]; then mkdir -p $(dirname $(AGDARSEC_HOME)); fi
endif
ifdef AGDARSEC_PR
	git clone $(AGDARSEC_REPO) $(AGDARSEC_HOME)
	cd $(AGDARSEC_HOME) \
		&& git fetch origin pull/$(AGDARSEC_PR)/head:pull-$(AGDARSEC_PR) \
		&& git checkout pull-$(AGDARSEC_PR)
else
	git clone --single-branch --branch $(AGDARSEC_BRANCH) $(AGDARSEC_REPO) $(AGDARSEC_HOME)
	cd $(AGDARSEC_HOME) && git checkout $(AGDARSEC_COMMIT_HASH)
ifeq (,$(findstring $(AGDARSEC_HOME),$(shell cat $(AGDA_LIBRARIES_FILE))))
	@echo $(AGDARSEC_HOME)/agdarsec.agda-lib >> $(AGDA_LIBRARIES_FILE)
endif
endif
endif

.PHONY: install-schmitty
install-schmitty: $(AGDA_LIBRARIES_FILE)
ifndef SCHMITTY_HOME
	@echo "Please set installation path using SCHMITTY_HOME:\n"
	@echo "  SCHMITTY_HOME=\$HOME/agda make install-schmitty"
else
ifneq ($(dirname $(SCHMITTY_HOME)),)
	if [ ! -d "$(dirname $(SCHMITTY_HOME))" ]; then mkdir -p $(dirname $(SCHMITTY_HOME)); fi
endif
ifdef SCHMITTY_PR
	git clone $(SCHMITTY_REPO) $(SCHMITTY_HOME)
	cd $(SCHMITTY_HOME) \
		&& git fetch origin pull/$(SCHMITTY_PR)/head:pull-$(SCHMITTY_PR) \
		&& git checkout pull-$(SCHMITTY_PR)
else
	git clone --single-branch --branch $(SCHMITTY_BRANCH) $(SCHMITTY_REPO) $(SCHMITTY_HOME)
	cd $(SCHMITTY_HOME) && git checkout $(SCHMITTY_COMMIT_HASH)
ifeq (,$(findstring $(SCHMITTY_HOME),$(shell cat $(AGDA_LIBRARIES_FILE))))
	@echo $(SCHMITTY_HOME)/schmitty.agda-lib >> $(AGDA_LIBRARIES_FILE)
endif
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
