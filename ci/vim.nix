{ pkgs ? import <nixpkgs> { }, version }:
with pkgs;

let
  python = python36;
  vimSrc = {
    "7.4" = {
      patch = "2367";
      sha256 = "sha256-M/otUhUfKEqIMdsm4vdJKjBcWPo/CokSqwKTHaAeauQ=";
    };
    "8.0" = {
      patch = "1850";
      sha256 = "sha256-YNYKp1KWGsQ+LghcgneHYXXd1yKdMLVnEV4w+woyw5o=";
    };
    "8.1" = {
      patch = "2424";
      sha256 = "sha256-uQAbLYfq6Fyittic7YzjU17vUYTuhvNHgkvOUi5xNbU=";
    };
    "8.2" = {
      patch = "5172";
      sha256 = "sha256-ycp9K7IpXBFLE9DV9/iQ+N1H7EMD/tP/KGv2VOXoDvE=";
    };
    "9.0" = {
      patch = "0048";
      sha256 = "sha256-3QG5yClSg5j17anxfWymyPOIy/89FMQp1ycLN7My7Zs=";
    };
  }.${version};
in stdenv.mkDerivation {
  name = "vim-${version}.${vimSrc.patch}";

  src = with vimSrc;
    fetchTarball {
      url = "https://github.com/vim/vim/archive/v${version}.${patch}.tar.gz";
      inherit sha256;
    };

  buildInputs = [ ncurses python ];

  configureFlags = [
    "--with-features=huge"
    "--enable-python3interp=yes"
    "--with-python3-config-dir=${python}/lib"
    "--with-python3-command=${python}/bin/python"
    "--disable-pythoninterp"
    "--disable-gui"
    "--enable-fail-if-missing"
  ];

  enableParallelBuilding = true;
  hardeningDisable = [ "fortify" ];
}
