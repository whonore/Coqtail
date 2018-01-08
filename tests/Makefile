# File: Makefile
# Author: Wolf Honore
# Description: Run test cases.

CODE_DIR := ../autoload
PYTEST = PYTHONPATH=$(CODE_DIR) python$* -m pytest $(PYTEST_OPT)
PYTEST_OPT := -q

.PHONY: test py py-cov indent

# All tests
test: py indent

# All Python tests with Python 2 and 3
py: py2 py3

# All Python tests with coverage with Python 2 and 3
py-cov: py2-cov py3-cov

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
	@$(PYTEST) --cov=$(CODE_DIR)

# Run indentation tests
indent:
	@echo "*******************"
	@echo "TESTING indentation"
	@echo "*******************"
	@vim -Nu vimrc -c 'Vader! indent.vader'
