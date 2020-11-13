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

  self = {
    inherit k;
    inherit mavenix;
  };

in self

