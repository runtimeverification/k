let
  sources = import ./nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = [ ( import ./nix/overlays/z3.nix ) ]; };
in

{ pkgs ? pinned

# Build an optimized release package.
# Currently requires dependents to use LTO. Use sparingly.
, release ? false
, haskell-backend ? null,
}:

let
  inherit (pkgs) callPackage;

  mavenix = import sources."mavenix" { inherit pkgs; };
  ttuegel = import sources."ttuegel" { inherit pkgs; };
  haskell-backend-project = 
    if haskell-backend != null then 
      import haskell-backend { inherit release; }
    else 
      import ./haskell-backend/src/main/native/haskell-backend {
        inherit release;
        src = ttuegel.cleanGitSubtree {
          src = ./.;
          subDir = "haskell-backend/src/main/native/haskell-backend";
        };
      };

  llvm-backend-project = import ./llvm-backend/src/main/native/llvm-backend {
    inherit pkgs;
    inherit release;
    src = ttuegel.cleanGitSubtree {
      name = "llvm-backend";
      src = ./.;
      subDir = "llvm-backend/src/main/native/llvm-backend";
    };
  };
  inherit (llvm-backend-project) clang llvm-backend;

  k = callPackage ./nix/k.nix {
    haskell-backend = haskell-backend-project.kore;
    prelude-kore = haskell-backend-project.prelude-kore;
    inherit llvm-backend mavenix;
    inherit (ttuegel) cleanGit cleanSourceWith;
  };

  self = {
    inherit k clang llvm-backend;
    haskell-backend = haskell-backend-project.kore;
    inherit mavenix;
    inherit (pkgs) mkShell;
  };

in self

