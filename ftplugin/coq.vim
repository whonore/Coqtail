" Supported versions (-1 means any number)
let s:supported = [
    \[8, 6, -1]
\]

" Check that Coq version is supported
" Assumes message is of the following form
" (where the 2nd ._ is optional and the 2nd . can be 'pl'):
" The Coq Proof Assistant, version _._._ (_ _)
let s:version = system("coqtop --version | awk '/version/{printf \"%s\", $6}'")
let s:versions = split(s:version, '\v(\.|pl)')

" Pad missing version numbers with 0
while len(s:versions) < 3
    let s:versions = add(s:versions, 0)
endwhile

let s:found_sup = 0
for s:supp in s:supported
    let s:is_sup = 1

    for s:idx in range(3)
        if s:supp[s:idx] != s:versions[s:idx] && s:supp[s:idx] != -1
            let s:is_sup = 0
            break
        endif
    endfor

    if s:is_sup
        let s:found_sup = 1
        break
    endif
endfor

call coqtail#Register(s:version, s:found_sup)
