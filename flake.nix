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
      overlays = system: [
        mavenix.overlay
        (final: prev: { llvm-backend-release = false; })
        llvm-backend.overlays.default
        haskell-backend.overlay
        (final: prev:
          let
            version =
              prev.haskell-backend-stackProject.hsPkgs.kore.components.exes.kore-exec.version;
            kore = prev.symlinkJoin {
              name = "kore-${version}-${haskell-backend.sourceInfo.shortRev}";
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
              debugger =
                if system == "x86_64-darwin" || system == "aarch64-darwin" then
                  prev.lldb
                else
                  prev.gdb;
              version = let
                package-version = prev.lib.removeSuffix "\n"
                  (builtins.readFile ./package/version);
              in "${package-version}-${self.rev or "dirty"}";
            };
          })
      ];
    in flake-utils.lib.eachSystem [
      "x86_64-linux"
      "x86_64-darwin"
      "aarch64-linux"
      "aarch64-darwin"
    ] (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = (overlays system);
        };
      in {
        inherit overlays;
        packages = {
          inherit (pkgs) k;

          checkVersions = let
            hashes = [
              {
                name = "llvm-mackend";
                rev = llvm-backend.rev;
              }
              {
                name = "haskell-mackend";
                rev = haskell-backend.rev;
              }
            ];
          in pkgs.writeShellScriptBin "checkVersions" ''
            STATUS=$(git submodule status);
            for elem in ${
              pkgs.lib.concatMapStringsSep " " ({ name, rev }: "${name},${rev}")
              hashes
            }; do
              IFS=","; set -- $elem;
              if ! grep -q "$2" <<< "$STATUS";
              then
                  echo "$1 with hash '$2' does not match any current submodules:"
                  git submodule status
                  exit 1
              fi
            done
            echo "All dependencies match"
          '';
        };
        defaultPackage = pkgs.k;
      }) // {
        overlays.llvm-backend = llvm-backend.overlays.default;
        overlays.haskell-backend = haskell-backend.overlay;
      };
}
