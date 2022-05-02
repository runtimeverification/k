let
  sources = import ./nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = []; };
in

{ pkgs ? pinned
, test ? null
}:

let
  inherit (pkgs) stdenv lib;
  inherit (pkgs) bison diffutils ncurses gmp mpfr libffi jemalloc;

  default = import ./. { inherit pkgs; };
  inherit (default) k haskell-backend llvm-backend;
  inherit (default) clang;

  ttuegel = import sources."ttuegel" { inherit pkgs ; };
  inherit (ttuegel) cleanGitSubtree;

in

stdenv.mkDerivation {
  name = "k-test";
  src = cleanGitSubtree {
    name = "k-distribution";
    src = ./.;
    subDir = "k-distribution";
  };
  preferLocalBuild = true;
  buildInputs = [
    diffutils ncurses bison clang gmp mpfr libffi jemalloc
    k haskell-backend llvm-backend
  ];
  postPatch = ''
    patchShebangs tests/regression-new
  '';
  buildFlags =
    [
      # Find executables on PATH
      "KOMPILE=kompile"
      "KRUN=krun"
      "KDEP=kdep"
      "KPROVE_LEGACY=kprove-legacy"
      "KPROVEX=kprovex"
      "KBMC=kbmc"
      "KAST=kast"
      "KPRINT=kprint"
      "KRUN_LEGACY=krun-legacy"
      "KEQ=keq"
      "KSERVER=kserver"
      "KPARSE=kparse"
      "KPARSE_GEN=kparse-gen"
      "KORE_PRINT=kore-print"
      "PACKAGE_VERSION=${lib.fileContents ./package/version}"
      "--output-sync"
    ]
    ++ lib.optional (test != null) "-C ${test}"
    ;
  enableParallelBuilding = true;
  preBuild = ''
    cd tests/regression-new
  '';
  installPhase = ''
    runHook preInstall

    touch "$out"

    runHook postInstall
  '';
}

