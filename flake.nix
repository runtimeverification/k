{
  description = "K Framework";
  inputs = {
    haskell-backend.url =
      "github:runtimeverification/haskell-backend/3bab611b2286dc3be4ce93c37e21581c68a1a8de";
    llvm-backend.url = "github:runtimeverification/llvm-backend";
    nixpkgs.follows = "haskell-backend/nixpkgs";
    llvm-backend.inputs.nixpkgs.follows = "haskell-backend/nixpkgs";
    flake-utils.follows = "haskell-backend/flake-utils";
    mavenix.url = "github:nix-community/mavenix";
  };

  outputs =
    { self, nixpkgs, flake-utils, haskell-backend, llvm-backend, mavenix }:
    let
      overlays = [
        mavenix.overlay
        (final: prev: { llvm-backend-release = false; })
        llvm-backend.overlays.default
        haskell-backend.overlay
        (final: prev:
          let
            version =
              prev.haskell-backend-stackProject.hsPkgs.kore.components.exes.kore-exec.version;
            kore = prev.symlinkJoin {
              name = "kore-${version}";
              paths = prev.lib.attrValues
                prev.haskell-backend-stackProject.hsPkgs.kore.components.exes;
            };

            src = prev.stdenv.mkDerivation {
              name = "llvm-source";
              src = prev.lib.cleanSource
                (prev.nix-gitignore.gitignoreSourcePure [ ] ./.);
              dontBuild = true;
              installPhase = ''
                mkdir $out
                cp -rv $src/* $out
                chmod -R u+w $out
                mkdir -p $out/llvm-backend/src/main/native/llvm-backend/matching
                cp -rv ${llvm-backend}/matching/* $out/llvm-backend/src/main/native/llvm-backend/matching
              '';
            };
          in {
            k = prev.callPackage ./nix/k.nix {
              inherit (prev) llvm-backend;
              mavenix = { inherit (prev) buildMaven; };
              haskell-backend = kore;
              inherit (haskell-backend) prelude-kore;
              inherit src;
            };
          })
      ];
    in flake-utils.lib.eachSystem [
      "x86_64-linux"
      "x86_64-darwin"
      "aarch64-linux"
      "aarch64-darwin"
    ] (system:
      let pkgs = import nixpkgs { inherit system overlays; };
      in {
        inherit overlays;
        packages = { inherit (pkgs) k; };
        defaultPackage = pkgs.k;
      }) // {
        overlays.llvm-backend = llvm-backend.overlays.default;
        overlays.haskell-backend = haskell-backend.overlay;
      };
}
