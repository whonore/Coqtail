{ pkgs ? import <nixpkgs> { }, version ? null, tox_version ? null }:
with builtins;

assert version != null || tox_version != null;
let
  pkg_urls = {
    "8.4" = "https://github.com/NixOS/nixpkgs/archive/18.03.tar.gz";
    "8.5" = "https://github.com/NixOS/nixpkgs/archive/24.05.tar.gz";
    "8.6" = "https://github.com/NixOS/nixpkgs/archive/24.05.tar.gz";
  };
  dot_version = if version != null then
    version
  else
    concatStringsSep "."
    (filter (s: s != "") (match "coq([0-9]|master)([0-9]*)-.*" tox_version));
  pkg_name = "coq_" + replaceStrings [ "." ] [ "_" ] dot_version;
in if hasAttr dot_version pkg_urls then
  (import (fetchTarball pkg_urls.${dot_version}) { }).${pkg_name}
else
  pkgs.coq.override ({ version = dot_version; })
