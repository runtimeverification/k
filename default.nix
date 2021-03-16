let
  sources = import ./nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = []; };
in

{ pkgs ? pinned }:

let
  ttuegel =
    let
      src = builtins.fetchGit {
        url = "https://github.com/ttuegel/nix-lib";
        rev = "66bb0ab890ff4d828a2dcfc7d5968465d0c7084f";
      };
    in import src { inherit pkgs; };
in

let
  inherit (pkgs) callPackage;

  mavenix = import sources."mavenix" { inherit pkgs; };

  llvm-backend-project = import ./llvm-backend/src/main/native/llvm-backend {
    inherit pkgs;
    src = ttuegel.cleanGitSubtree {
      name = "llvm-backend";
      src = ./.;
      subDir = "llvm-backend/src/main/native/llvm-backend";
    };
  };
  inherit (llvm-backend-project) clang llvm-backend;

  k = callPackage ./nix/k.nix {
    inherit haskell-backend llvm-backend mavenix;
  };

  haskell-backend-project = import ./haskell-backend/src/main/native/haskell-backend {
    src = ttuegel.cleanGitSubtree {
      src = ./.;
      subDir = "haskell-backend/src/main/native/haskell-backend";
    };
  };
  haskell-backend = haskell-backend-project.kore;

  self = {
    inherit k clang llvm-backend haskell-backend;
    inherit mavenix;
    inherit (pkgs) mkShell;
  };

in self

