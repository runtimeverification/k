# This is a shell just for updating Maven.

let
  sources = import ../nix/sources.nix;
  pinned = import sources."nixpkgs" {
    config = { };
    overlays = [ ];
  };

in { pkgs ? pinned }:

let
  inherit (pkgs) mkShell;

  default = import ../. { inherit pkgs; };
  inherit (default) mavenix;

in mkShell { buildInputs = [ mavenix.cli ]; }
