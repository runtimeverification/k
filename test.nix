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
  configurePhase = ''
    export KSERVER_SOCKET=$NIX_BUILD_TOP/kserver-socket
    KSERVER_LOG=$NIX_BUILD_TOP/kserver.log
  '';
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
      "KRUN_LEGACY=krun-legacy"
      "KEQ=keq"
      "KSERVER=kserver"
      "--output-sync"
    ]
    ++ lib.optional (test != null) "-C ${test}"
    ;
  enableParallelBuilding = true;
  preBuild = ''
    spawn-kserver $KSERVER_LOG
    cd tests/regression-new
  '';
  postBuild = ''
    stop-kserver
    sleep 4
    cat $KSERVER_LOG
  '';
  installPhase = ''
    runHook preInstall

    touch "$out"

    runHook postInstall
  '';
}

