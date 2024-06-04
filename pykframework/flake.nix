{
  description = "Application packaged using poetry2nix";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    poetry2nix = {
      url =
        "github:nix-community/poetry2nix/626111646fe236cb1ddc8191a48c75e072a82b7c";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.follows = "poetry2nix/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, poetry2nix }:
    {
      # Nixpkgs overlay providing the application
      overlay = final: prev:
        let
          mkpykframework = python:
            let
              p2n = poetry2nix.lib.mkPoetry2Nix { pkgs = prev; };
            in p2n.mkPoetryApplication {
              python = python;
              projectDir = ./.;
              groups = [ ];
              # We remove `"dev"` from `checkGroups`, so that poetry2nix does not try to resolve dev dependencies.
              checkGroups = [ ];
              overrides = p2n.defaultPoetryOverrides.extend
                (self: super: {
                  pygments = super.pygments.overridePythonAttrs
                  (
                    old: {
                      buildInputs = (old.buildInputs or [ ]) ++ [ super.hatchling ];
                    }
                  );
                });
            };
        in rec {
          pykframework = pykframework-python310;
          pykframework-python310 = mkpykframework prev.python310;
          pykframework-python311 = mkpykframework prev.python311;
        };
    } // (flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlay ];
        };
      in {
        packages = {
          inherit (pkgs) pykframework pykframework-python310 pykframework-python311;
          default = pkgs.pykframework;
        };
      }));
}
