# File: Makefile
# Author: Wolf Honore
# Description: Run test cases.

MAKE := $(MAKE) --no-print-directory
CODE_DIR := ../autoload
PYTEST = PYTHONPATH=$(CODE_DIR) python$* -m pytest $(PYTEST_OPT)
PYTEST_OPT += -q

PYV := 2 3
PYS := $(addprefix py, $(PYV))

COQV := 8_4 8_5 8_6 8_7 8_8
COQS := $(addprefix coq_, $(COQV))

COQ_PYS := $(foreach PY, $(PYS), $(foreach COQ, $(COQS), $(COQ)-$(PY)))

.PHONY: test py py-cov coq-py indent

# All tests
test: py indent

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
	@echo "*************"
	@echo "USING $(COQ)"
	@echo "*************"
	@nix-shell -p $(COQ) --run "$(MAKE) $(PY)"

# Run indentation tests
indent:
	@echo "*******************"
	@echo "TESTING indentation"
	@echo "*******************"
	@vim -Nu vimrc -c 'Vader! indent.vader'
