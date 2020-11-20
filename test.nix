let
  sources = import ./nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = []; };
in

{ pkgs ? pinned }:

let
  inherit (pkgs) stdenv;
  inherit (pkgs) bison diffutils ncurses gmp mpfr libffi jemalloc;

  default = import ./. { inherit pkgs; };
  inherit (default) k haskell-backend llvm-backend;
  inherit (default) clang;

in

stdenv.mkDerivation {
  name = "k-test";
  src = ./k-distribution;
  preferLocalBuild = true;
  buildInputs = [
    diffutils ncurses bison clang gmp mpfr libffi jemalloc
    k haskell-backend llvm-backend
  ];
  postPatch = ''
    patchShebangs tests/regression-new
  '';
  configurePhase = "true";
  buildFlags = [
    "KOMPILE=kompile"
    "KRUN=krun"
    "KDEP=kdep"
    "KPROVE=kprove"
    "KBMC=kbmc"
    "KAST=kast"
    "KPRINT=kprint"
    "KX=kx"
  ];
  buildPhase = ''
    runHook preBuild

    cd k-distribution/tests/regression-new
    make $buildFlags -j4

    runHook postBuild
  '';
  installPhase = ''
    runHook preInstall

    mkdir -p "$out"
    cp -a -t "$out" .

    runHook postInstall
  '';
}

