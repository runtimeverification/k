let
  sources = import ./nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = []; };
in

{ pkgs ? pinned }:

let
  inherit (pkgs) callPackage nix-gitignore;

  mavenix = import sources."mavenix" { inherit pkgs; };

  k = callPackage ./nix/k.nix {
    inherit mavenix;
  };

  llvm-backend-project = import ./llvm-backend/src/main/native/llvm-backend { inherit pkgs; };
  inherit (llvm-backend-project) clang llvm-backend;

  haskell-backend-project = import ./haskell-backend/src/main/native/haskell-backend {};
  haskell-backend = haskell-backend-project.kore;

  self = {
    inherit k clang llvm-backend haskell-backend;
    inherit mavenix;
  };

in self

