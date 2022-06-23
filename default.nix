let
  sources = import ./nix/sources.nix;
  pinned = import sources."nixpkgs" {
    config = { };
    overlays = [ (import ./nix/overlays/z3.nix) ];
  };

in { pkgs ? pinned

  # Build an optimized release package.
  # Currently requires dependents to use LTO. Use sparingly.
, release ? false }:

let
  inherit (pkgs) callPackage;

  mavenix = import sources."mavenix" { inherit pkgs; };
  ttuegel = import sources."ttuegel" { inherit pkgs; };

  llvm-backend-project = import ./llvm-backend/src/main/native/llvm-backend {
    inherit pkgs;
    inherit release;
    src = ttuegel.cleanGitSubtree {
      name = "llvm-backend";
      src = ./.;
      subDir = "llvm-backend/src/main/native/llvm-backend";
    };
  };
  inherit (llvm-backend-project) llvm-backend;
  inherit (pkgs) clang;

  k = callPackage ./nix/k.nix {
    src = ttuegel.cleanSourceWith {
      name = "k";
      src = ttuegel.cleanGit {
        src = ./.;
        name = "k";
      };
      ignore = [
        "result*"
        "nix/"
        "*.nix"
        "haskell-backend/src/main/native/haskell-backend/*"
        "llvm-backend/src/main/native/llvm-backend/*"
        "!llvm-backend/src/main/native/llvm-backend/matching" # need pom.xml
        "k-distribution/tests/regression-new"
      ];
    };
    inherit haskell-backend llvm-backend mavenix prelude-kore;
    debugger =
      if pkgs.system == "x86_64-darwin" || pkgs.system == "aarch64-darwin" then
        pkgs.lldb
      else
        pkgs.gdb;
    version = pkgs.lib.removeSuffix "\n" (builtins.readFile ./package/version);
  };

  haskell-backend-project =
    import ./haskell-backend/src/main/native/haskell-backend {
      src = ttuegel.cleanGitSubtree {
        src = ./.;
        subDir = "haskell-backend/src/main/native/haskell-backend";
      };
    };
  haskell-backend = haskell-backend-project.kore;
  inherit (haskell-backend-project) prelude-kore;

  self = {
    inherit k clang llvm-backend haskell-backend;
    inherit mavenix;
    inherit (pkgs) mkShell;

    dummy = pkgs.stdenv.mkDerivation {
      name = "dummy";
      src = ./package;
      installPhase = ''cp $src/version $out'';
    };
  };

in self

