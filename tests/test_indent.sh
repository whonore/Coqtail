#!/bin/sh

vim -c 'norm gg=G' -c 'w! indent_tmp.v' -c 'q!' unindented.v
diff indent_correct.v indent_tmp.v
rm indent_tmp.v
