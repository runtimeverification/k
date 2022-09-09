{
  description = "Application packaged using poetry2nix";

  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs";
  inputs.poetry2nix.url = "github:nix-community/poetry2nix";

  outputs = { self, nixpkgs, flake-utils, poetry2nix }:
    {
      # Nixpkgs overlay providing the application
      overlay = final: prev: {
        pyk = prev.poetry2nix.mkPoetryApplication { 
          python = prev.python39;
          projectDir = ./.; 
        };
      };
    } // (flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ poetry2nix.overlay self.overlay ];
        };
      in {
        packages = {
          pyk = pkgs.pyk;
          default = pkgs.pyk;
        };
      }));
}
