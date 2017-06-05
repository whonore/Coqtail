" Check that Coq version is 8.6
if !empty(system('coqtop --version | grep 8.6'))
    call coqtail#Register()
else
    echoerr "Coqtail requires Coq version 8.6."
endif
