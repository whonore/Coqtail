{ pkgs ? import <nixpkgs> {}, version }:
with pkgs;

let
  vimSrc = {
    "7.4" = {
      patch = "2367";
      sha256 = "1r3a3sh1v4q2mc98j2izz9c5qc1a97vy49nv6644la0z2m92vyik";
    };
    "8.0" = {
      patch = "1850";
      sha256 = "16n3685gnc2y25kvac4x4bbxsxb1hxvq4p085qzc86lnaakhmmk0";
    };
    "8.1" = {
      patch = "2424";
      sha256 = "1d9mf4p55kjbh93z71pfhi8yypjkwf6fv76qnsi5rs7ahwnin05r";
    };
    "8.2" = {
      patch = "1770";
      sha256 = "14mbrbnjwb8r4pl06vafd56x0pmbcgqvr57s2ns2arh7xcy9bri7";
    };
  }.${version};
in stdenv.mkDerivation {
  name = "vim";

  src = with vimSrc; fetchTarball {
    url = "https://github.com/vim/vim/archive/v${version}.${patch}.tar.gz";
    inherit sha256;
  };

  buildInputs = [ncurses python36];

  configureFlags = [
    "--with-features=huge"
    "--enable-python3interp=yes"
    "--with-python3-config-dir=${python36}/lib"
    "--disable-python2interp"
    "--disable-gui"
    "--enable-fail-if-missing"
  ];

  enableParallelBuilding = true;
  hardeningDisable = ["fortify"];
}
