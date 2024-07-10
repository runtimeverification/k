{
  description = "Application packaged using poetry2nix";

  inputs = {
    rv-utils.url = "github:runtimeverification/rv-nix-tools";
    nixpkgs.follows = "rv-utils/nixpkgs";
    poetry2nix = {
      url =
        "github:nix-community/poetry2nix/626111646fe236cb1ddc8191a48c75e072a82b7c";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.follows = "poetry2nix/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, rv-utils, poetry2nix }:
    {
      # Nixpkgs overlay providing the application
      overlay = (import ../nix/pyk-overlay.nix {
        inherit poetry2nix;
        projectDir = ./.;
      });
    } // (flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlay ];
        };
      in {
        packages = {
          inherit (pkgs) pyk pyk-python310 pyk-python311;
          default = pkgs.pyk;
        };
      }));
}
