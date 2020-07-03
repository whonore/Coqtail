#!/usr/bin/env bash

version="$1"
outdir="$2"
if [ -z "$outdir" ]; then exit 1; fi
outdir="$outdir/coq"

function master {
    path=$(nix-prefetch-url --unpack 'https://github.com/coq/coq-on-cachix/tarball/master' --name source --print-path | tail -n1)
    nix-build -j auto "$path" --extra-substituters "https://coq.cachix.org" --trusted-public-keys "cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= coq.cachix.org-1:5QW/wwEnD+l2jvN6QRbRRsa4hBHG3QiQQ26cxu1F5tI=" -o "$outdir"
    exit
}

pkgs='<nixpkgs>'
case $version in
    *coq84*) pkgs='https://github.com/NixOS/nixpkgs/archive/18.03.tar.gz'; attr=coq_8_4;;
    *coq85*) attr=coq_8_5;;
    *coq86*) attr=coq_8_6;;
    *coq87*) attr=coq_8_7;;
    *coq88*) attr=coq_8_8;;
    *coq89*) attr=coq_8_9;;
    *coq810*) attr=coq_8_10;;
    *coq811*) attr=coq_8_11;;
    *coqmaster*) master;;
    *) exit 1;;
esac

nix-build -j auto "$pkgs" -A "$attr" -o "$outdir"
