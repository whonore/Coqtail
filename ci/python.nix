{ pkgs ? import <nixpkgs> {}, toxenv }:
with pkgs; with lib.strings;

let py = if hasInfix "py2" toxenv then python2 else python3; in
py.withPackages (ps: [ps.tox])
