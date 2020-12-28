#!/bin/sh
vim -Nu vimrc -c 'py3 import sys; print(sys.version); print(sys.path)'
vim -Nu vimrc -c 'Vader! *.vader'
