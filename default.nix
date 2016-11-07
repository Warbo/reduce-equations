{ mkDerivation, aeson, base, bytestring, containers, directory
, haskell-src-exts, mlspec-helper, mtl, nix-eval, QuickCheck
, quickspec, stdenv, stringable, tasty, tasty-quickcheck, text
, transformers
}:
mkDerivation {
  pname = "reduce-equations";
  version = "0.1.0.5";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base bytestring haskell-src-exts mlspec-helper mtl nix-eval
    QuickCheck quickspec stringable text transformers
  ];
  executableHaskellDepends = [ aeson base ];
  testHaskellDepends = [
    aeson base bytestring containers directory haskell-src-exts
    nix-eval QuickCheck quickspec stringable tasty tasty-quickcheck
  ];
  homepage = "http://chriswarbo.net/git/reduce-equations";
  description = "Simplify a set of equations by removing redundancies";
  license = stdenv.lib.licenses.publicDomain;
}
