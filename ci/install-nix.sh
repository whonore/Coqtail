#!/usr/bin/env bash
# Taken from https://github.com/pallavagarwal07/NixCI

sudo apt-get update
sudo apt-get -y install bzip2 curl bash

cd "${HOME}"
bash <(curl https://nixos.org/nix/install)
mkdir -p ${HOME}/.nixpkgs
echo '{
  nix.binaryCaches = ["http://hydra.nixos.org/" "http://cache.nixos.org/"];
}' > ${HOME}/.nixpkgs/config.nix
