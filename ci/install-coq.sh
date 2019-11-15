#!/usr/bin/env bash

version="$1"
outdir="$2"

pkgs='<nixpkgs>'
case $version in
    *coq84*) pkgs='https://github.com/NixOS/nixpkgs/archive/18.03.tar.gz'; attr=coq_8_4;;
    *coq85*) attr=coq_8_5;;
    *coq86*) attr=coq_8_6;;
    *coq87*) attr=coq_8_7;;
    *coq88*) attr=coq_8_8;;
    *coq89*) attr=coq_8_9;;
    *coq810*) pkgs='https://github.com/NixOS/nixpkgs/archive/19.09.tar.gz'; attr=coq_8_10;;
    *) exit 1;;
esac

nix-build -j auto "$pkgs" -A "$attr" -o "$outdir/coq"
