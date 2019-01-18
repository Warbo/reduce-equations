with builtins;
with rec {
  # A known-good pinned nixpkgs version
  nixpkgs = overlays: import (fetchTarball {
    name   = "nixpkgs1709";
    url    = https://github.com/NixOS/nixpkgs/archive/17.09.tar.gz;
    sha256 = "0kpx4h9p1lhjbn1gsil111swa62hmjs9g93xmsavfiki910s73sh";
  }) { inherit overlays; config = {}; };

  # Avoid rebuilding if only our metadata has changed
  src = filterSource (path: _: !(elem (baseNameOf path)) [
                       ".git" ".gitignore" ".issues" "dist" "dist-newstyle"
                       "nixpkgs.nix" "README" "release.nix" "shell.nix"
                       "test.sh"
                     ])
                     ./.;

  # Overrides the pinned haskellPackages set. We don't do it directly in an
  # overlay, since that can break the dependencies of cabal2nix.
  haskellPackages =
    with nixpkgs [];
    haskell.packages.ghc7103.override (old: {
      overrides = self: super: {
        QuickCheck       = self.callHackage "QuickCheck" "2.8.2" {};

        reduce-equations = self.callPackage (super.haskellSrc2nix {
          inherit src;
          name = "reduce-equations";
        }) {};
      };
    });
};
nixpkgs [
  (self: super: { inherit haskellPackages; })
]
