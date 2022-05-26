{
  description = "K Framework";
  inputs = {
    haskell-backend.url = "github:runtimeverification/haskell-backend/e315e34fc61390f786bac543daf3d6715567e640";
    llvm-backend.url = "github:runtimeverification/llvm-backend/c3b4d54eec8fe7079e6fc085322b09334a629c61";
    nixpkgs.follows = "haskell-backend/nixpkgs";
    llvm-backend.inputs.nixpkgs.follows = "haskell-backend/nixpkgs";
    flake-utils.follows = "haskell-backend/flake-utils";
    mavenix.url = "github:nix-community/mavenix";
  };

  outputs = { self, nixpkgs, flake-utils, haskell-backend, llvm-backend, mavenix }:
    let
      overlays = [
        mavenix.overlay
        (final: prev: 
          { release = false; }
        )
        llvm-backend.overlay
        haskell-backend.overlay
        (final: prev: 
          let 
            version = prev.k-haskell-backend.kore.components.exes.kore-exec.version;
            kore = prev.symlinkJoin {
              name = "kore-${version}";
              paths = prev.lib.attrValues prev.k-haskell-backend.kore.components.exes;
            };

            src = prev.stdenv.mkDerivation {
              name = "llvm-source";
              src = prev.lib.cleanSource (prev.nix-gitignore.gitignoreSourcePure [] ./.);
              dontBuild = true;
              installPhase = ''
                mkdir $out
                cp -rv $src/* $out
                chmod -R u+w $out
                mkdir -p $out/llvm-backend/src/main/native/llvm-backend/matching
                cp -rv ${llvm-backend}/matching/* $out/llvm-backend/src/main/native/llvm-backend/matching
              '';
            };
          in
          {
            k = prev.callPackage ./nix/k.nix {
              inherit (prev) llvm-backend;
              mavenix = {inherit (prev) buildMaven; };
              haskell-backend = kore;
              inherit (haskell-backend) prelude-kore;
              inherit src;
            };
          }
        )
      ];
    in
      flake-utils.lib.eachSystem [ "x86_64-linux" "x86_64-darwin"  "aarch64-linux"  "aarch64-darwin"  ] (system:
        let
          pkgs = import nixpkgs { inherit system overlays; };
        in
          {
            inherit overlays;
            packages = { inherit (pkgs) k; };
            defaultPackage = pkgs.k;
          }
      );
}