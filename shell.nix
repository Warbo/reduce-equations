with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "dummy";
  buildInputs = [ (haskell.packages.ghc7103.ghcWithPackages (h: [])) ];
}
