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
  buildFlags =
    [
      # Find executables on PATH
      "KOMPILE=kompile"
      "KRUN=krun"
      "KDEP=kdep"
      "KPROVE=kprove"
      "KBMC=kbmc"
      "KAST=kast"
      "KPRINT=kprint"
      "KX=kx"
      "KEQ=keq"
      "KSERVER=kserver"
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

    mkdir -p "$out"
    cp -a -t "$out" .

    runHook postInstall
  '';
}

