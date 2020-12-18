let
  sources = import ./nix/sources.nix;
  pinned = import sources."nixpkgs" { config = {}; overlays = []; };
in

{ pkgs ? pinned }:

let
  inherit (pkgs) mkShell;

  default = import ./. { inherit pkgs; };
  inherit (default) k clang llvm-backend haskell-backend;
  inherit (default) mavenix;

in mkShell {
  inputsFrom = [
    k
  ];

  buildInputs = [
    clang llvm-backend
    haskell-backend
    mavenix.cli
  ];
}
