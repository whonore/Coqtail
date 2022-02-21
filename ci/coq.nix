{ pkgs ? import <nixpkgs> { }, version ? null, tox_version ? null }:
with builtins;

assert version != null || tox_version != null;
let
  url_8_4 = "https://github.com/NixOS/nixpkgs/archive/18.03.tar.gz";
  dot_version = if version != null then
    version
  else
    concatStringsSep "."
    (filter (s: s != "") (match "coq([0-9]|master)([0-9]*)-.*" tox_version));
in if dot_version == "8.4" then
  (import (fetchTarball url_8_4) { }).coq_8_4
else if dot_version == "master" then
  # NOTE: Temporary workaround until
  # https://github.com/coq-community/coq-nix-toolbox/issues/95 is resolved
  (pkgs.coq.override { version = dot_version; }).overrideAttrs (old: {
    postInstall = old.postInstall + ''
      for prog in $out/bin/coq*; do
        wrapProgram $prog --prefix OCAMLPATH : $OCAMLPATH
      done
    '';
  })
else
  pkgs.coq.override ({ version = dot_version; })
