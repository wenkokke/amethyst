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


#########################
# Generate Docker Image #
#########################

.PHONY: docker-image
docker-image: amethyst.tar

amethyst.tar: Dockerfile $(AGDA_FILES)
	docker build --tag amethyst:latest .
	docker save -o amethyst.tar amethyst:latest


########################
# Install Dependencies #
########################

CABAL_DIR ?= $(HOME)/.cabal

AGDA_DIR ?= $(HOME)/.agda
AGDA_LIBRARIES_FILE := $(AGDA_DIR)/libraries
AGDA_EXECUTABLES_FILE := $(AGDA_DIR)/executables

AGDA_HOME ?= $(AGDA_DIR)/agda
AGDA_REPO ?= https://github.com/agda/agda
AGDA_PR ?=
AGDA_BRANCH ?= master
AGDA_COMMIT_HASH ?= FETCH_HEAD
ifdef AGDA_PR
AGDA_LOCK := $(AGDA_HOME)/pr-$(AGDA_PR).lock
else
AGDA_LOCK := $(AGDA_HOME)/$(AGDA_BRANCH)-$(AGDA_COMMIT_HASH).lock
endif

AGDA_STDLIB_HOME ?= $(AGDA_DIR)/standard-library
AGDA_STDLIB_REPO ?= https://github.com/agda/agda-stdlib
AGDA_STDLIB_PR ?=
AGDA_STDLIB_BRANCH ?= experimental
AGDA_STDLIB_COMMIT_HASH ?= FETCH_HEAD
ifdef AGDA_STDLIB_PR
AGDA_STDLIB_LOCK := $(AGDA_STDLIB_HOME)/pr-$(AGDA_STDLIB_PR).lock
else
AGDA_STDLIB_LOCK := $(AGDA_STDLIB_HOME)/$(AGDA_STDLIB_BRANCH)-$(AGDA_STDLIB_COMMIT_HASH).lock
endif

AGDARSEC_HOME ?= $(AGDA_DIR)/agdarsec
AGDARSEC_REPO ?= https://github.com/gallais/agdarsec
AGDARSEC_PR ?=
AGDARSEC_BRANCH ?= master
AGDARSEC_COMMIT_HASH ?= FETCH_HEAD
ifdef AGDARSEC_PR
AGDARSEC_LOCK := $(AGDARSEC_HOME)/pr-$(AGDARSEC_PR).lock
else
AGDARSEC_LOCK := $(AGDARSEC_HOME)/$(AGDARSEC_BRANCH)-$(AGDARSEC_COMMIT_HASH).lock
endif

SCHMITTY_HOME ?= $(AGDA_DIR)/schmitty
SCHMITTY_REPO ?= https://github.com/wenkokke/schmitty
SCHMITTY_BRANCH ?= master
SCHMITTY_PR ?=
SCHMITTY_COMMIT_HASH ?= FETCH_HEAD
ifdef SCHMITTY_PR
SCHMITTY_LOCK := $(SCHMITTY_HOME)/pr-$(SCHMITTY_PR).lock
else
SCHMITTY_LOCK := $(SCHMITTY_HOME)/$(SCHMITTY_BRANCH)-$(SCHMITTY_COMMIT_HASH).lock
endif


################
# Install Agda #
################

.PHONY: install-agda
install-agda: $(CABAL_DIR)/bin/agda

$(AGDA_LOCK): $(AGDA_LIBRARIES_FILE)
	rm -rf $(AGDA_HOME)
	mkdir -p $(AGDA_HOME)
	cd $(AGDA_HOME) \
		&& git init \
		&& git remote add origin $(AGDA_REPO)
ifdef AGDA_PR
	cd $(AGDA_HOME) \
		&& git fetch origin pull/$(AGDA_PR)/head:pull-$(AGDA_PR) \
		&& git checkout pull-$(AGDA_PR)
else
	cd $(AGDA_HOME) \
		&& git fetch origin $(AGDA_BRANCH) \
		&& git checkout $(AGDA_COMMIT_HASH)
endif
	cd $(AGDA_HOME) \
		&& git submodule update --init src/fix-whitespace
	touch $(AGDA_LOCK)

$(CABAL_DIR)/bin/agda: $(AGDA_LOCK)
	cd $(AGDA_HOME) \
		&& cabal v1-install \
			--disable-documentation \
			--disable-library-profiling \
			-fenable-cluster-counting \
			--ghc-options="+RTS -M4G -RTS"

$(AGDA_LIBRARIES_FILE):
	mkdir -p $(AGDA_DIR)
	touch $(AGDA_LIBRARIES_FILE)

$(AGDA_EXECUTABLES_FILE):
	mkdir -p $(AGDA_DIR)
	touch $(AGDA_EXECUTABLES_FILE)


############################
# Install Standard Library #
############################

.PHONY: install-agda-stdlib
install-agda-stdlib: $(AGDA_STDLIB_LOCK)

.PHONY: uninstall-agda-stdlib
uninstall-agda-stdlib:
	rm -rf $(AGDA_STDLIB_HOME)

$(AGDA_STDLIB_LOCK): $(AGDA_LIBRARIES_FILE)
	rm -rf $(AGDA_STDLIB_HOME)
	mkdir -p $(AGDA_STDLIB_HOME)
	cd $(AGDA_STDLIB_HOME) \
		&& git init \
		&& git remote add origin $(AGDA_STDLIB_REPO)
ifdef AGDA_STDLIB_PR
	cd $(AGDA_STDLIB_HOME) \
		&& git fetch origin pull/$(AGDA_STDLIB_PR)/head:pull-$(AGDA_STDLIB_PR) \
		&& git checkout pull-$(AGDA_STDLIB_PR)
else
	cd $(AGDA_STDLIB_HOME) \
		&& git fetch origin $(AGDA_STDLIB_BRANCH) \
		&& git checkout $(AGDA_STDLIB_COMMIT_HASH)
endif
ifeq (,$(findstring $(AGDA_STDLIB_HOME),$(shell cat $(AGDA_LIBRARIES_FILE))))
	@echo $(AGDA_STDLIB_HOME)/standard-library.agda-lib >> $(AGDA_LIBRARIES_FILE)
endif
	touch $(AGDA_STDLIB_LOCK)


####################
# Install Agdarsec #
####################

.PHONY: install-agdarsec
install-agdarsec: $(AGDARSEC_LOCK)

.PHONY: uninstall-agdarsec
uninstall-agdarsec:
	rm -rf $(AGDARSEC_HOME)

$(AGDARSEC_LOCK): $(AGDA_LIBRARIES_FILE)
	rm -rf $(AGDARSEC_HOME)
	mkdir -p $(AGDARSEC_HOME)
	cd $(AGDARSEC_HOME) \
		&& git init \
		&& git remote add origin $(AGDARSEC_REPO)
ifdef AGDARSEC_PR
	cd $(AGDARSEC_HOME) \
		&& git fetch origin pull/$(AGDARSEC_PR)/head:pull-$(AGDARSEC_PR) \
		&& git checkout pull-$(AGDARSEC_PR)
else
	cd $(AGDARSEC_HOME) \
		&& git fetch origin $(AGDARSEC_BRANCH) \
		&& git checkout $(AGDARSEC_COMMIT_HASH)
endif
ifeq (,$(findstring $(AGDARSEC_HOME),$(shell cat $(AGDA_LIBRARIES_FILE))))
	@echo $(AGDARSEC_HOME)/agdarsec.agda-lib >> $(AGDA_LIBRARIES_FILE)
endif
	touch $(AGDARSEC_LOCK)


####################
# Install Schmitty #
####################

.PHONY: install-schmitty
install-schmitty: $(SCHMITTY_LOCK)

.PHONY: uninstall-schmitty
uninstall-schmitty:
	rm -rf $(SCHMITTY_HOME)

$(SCHMITTY_LOCK): $(AGDA_LIBRARIES_FILE)
	rm -rf $(SCHMITTY_HOME)
	mkdir -p $(SCHMITTY_HOME)
	cd $(SCHMITTY_HOME) \
		&& git init \
		&& git remote add origin $(SCHMITTY_REPO)
ifdef SCHMITTY_PR
	cd $(SCHMITTY_HOME) \
		&& git fetch origin pull/$(SCHMITTY_PR)/head:pull-$(SCHMITTY_PR) \
		&& git checkout pull-$(SCHMITTY_PR)
else
	cd $(SCHMITTY_HOME) \
		&& git fetch origin $(SCHMITTY_BRANCH) \
		&& git checkout $(SCHMITTY_COMMIT_HASH)
endif
ifeq (,$(findstring $(SCHMITTY_HOME),$(shell cat $(AGDA_LIBRARIES_FILE))))
	@echo $(SCHMITTY_HOME)/schmitty.agda-lib >> $(AGDA_LIBRARIES_FILE)
endif
	touch $(SCHMITTY_LOCK)


########################
# Register SMT Solvers #
########################

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

###################
# Install Marabou #
###################

MARABOU := vendor/Marabou/build/Marabou

vendor/Marabou:
	git submodule init
	git submodule update --recursive

$(MARABOU): vendor/Marabou
	cd vendor/Marabou \
		&& mkdir build  \
		&& cd build     \
		&& cmake ..     \
		&& cmake --build .

