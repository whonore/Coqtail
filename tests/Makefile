# File: Makefile
# Author: Wolf Honore
# Description: Run test cases.

MAKE := $(MAKE) --no-print-directory
CODE_DIR := ../autoload
PYTEST = PYTHONPATH=$(CODE_DIR) python$* -m pytest $(PYTEST_OPT)
PYTEST_OPT += -q

PYV := 2 3
PYS := $(addprefix py, $(PYV))

COQV := 8_4 8_5 8_6 8_7 8_8 8_9
COQS := $(addprefix coq_, $(COQV))
# coq_8_4 is no longer in the default nixpkgs so have to use an archived version
COQ4_PKGS := https://github.com/NixOS/nixpkgs/archive/18.03.tar.gz

COQ_PYS := $(foreach PY, $(PYS), $(foreach COQ, $(COQS), $(COQ)-$(PY)))

VIM_TESTS := indent coq_project

.PHONY: test py py-cov coq-py vim $(VIM_TESTS)

# All tests
test: py vim

# All Python tests with Python 2 and 3
py: $(PYS)

# All Python tests with coverage with Python 2 and 3
py-cov: $(addsuffix -cov, $(PYS))

# All versions of Coq and all versions of Python
coq-py: $(COQ_PYS)

# All versions of Coq with a particular Python
$(addprefix coq-, $(PYS)):
	@$(eval PY := $(lastword $(subst -, , $@)))
	@$(MAKE) $(addsuffix -$(PY), $(COQS))

# All versions of Python with a particular Coq
$(addsuffix -py, $(COQS)):
	@$(eval COQ := $(firstword $(subst -, , $@)))
	@$(MAKE) $(addprefix $(COQ)-, $(PYS))

# Run Python tests with version %
py%:
	@echo "***************"
	@echo "TESTING python$*"
	@echo "***************"
	@$(PYTEST)

# Run Python tests with coverage with version %
py%-cov:
	@echo "************************"
	@echo "TESTING python$* coverage"
	@echo "************************"
	@$(PYTEST) --cov=$(CODE_DIR) --cov-branch

# Run a Python test with a particular Coq version using nix
$(COQ_PYS):
	@$(eval COQ := $(firstword $(subst -, , $@)))
	@$(eval PY := $(lastword $(subst -, , $@)))
	$(eval PKGS := $(if $(findstring coq_8_4, $@), -I nixpkgs=$(COQ4_PKGS),))
	@echo "*************"
	@echo "USING $(COQ)"
	@echo "*************"
	@nix-shell $(PKGS) -p $(COQ) --run "$(MAKE) $(PY)"

# All Vim tests
vim: $(VIM_TESTS)

# Run Vim tests
$(VIM_TESTS):
	@echo "*******************"
	@echo "TESTING $@"
	@echo "*******************"
	@vim -Nu vimrc -c 'Vader! $@.vader'
