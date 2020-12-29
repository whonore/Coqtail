{ pkgs ? import <nixpkgs> {}, version ? null, tox_version ? null }:
with builtins;

assert version != null || tox_version != null;
let
  dot_version = if version != null then version
                  else concatStringsSep "."
                         (filter (s: s != "")
                           (match "coq([0-9]|master)([0-9]*)-.*" tox_version));
  coq = "coq_" + replaceStrings ["."] ["_"] dot_version;
  coqpkgs = if dot_version == "8.4"
            then (import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/18.03.tar.gz") {})
            else pkgs;
in
  if hasAttr coq coqpkgs
  then getAttr coq coqpkgs
  else if dot_version == "master"
       then (import (fetchTarball https://github.com/coq/coq-on-cachix/tarball/master) {})
       else abort "Invalid version ${dot_version}"
