{
  description = "K Framework";
  inputs = {
    haskell-backend.url = "github:runtimeverification/haskell-backend";
    llvm-backend.url = "github:runtimeverification/llvm-backend";
    nixpkgs.follows = "haskell-backend/nixpkgs";
    llvm-backend.inputs.nixpkgs.follows = "haskell-backend/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    mavenix.url = "github:goodlyrottenapple/mavenix";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    pynixify.url = "github:goodlyrottenapple/pynixify";
  };

  outputs = { self, nixpkgs, flake-utils, haskell-backend, llvm-backend, mavenix
    , flake-compat, pynixify }:
    let
      allOverlays = [
        mavenix.overlay
        llvm-backend.overlays.default
        haskell-backend.overlay
        (final: prev:
          let
            kore-version =
              prev.haskell-backend-stackProject.hsPkgs.kore.components.exes.kore-exec.version;
            kore = prev.symlinkJoin {
              name = "kore-${kore-version}-${
                  haskell-backend.sourceInfo.shortRev or "local"
                }";
              paths = prev.lib.attrValues
                prev.haskell-backend-stackProject.hsPkgs.kore.components.exes;
            };
            k-version =
              prev.lib.removeSuffix "\n" (builtins.readFile ./package/version);
            src = prev.stdenv.mkDerivation {
              name = "k-${k-version}-${self.rev or "dirty"}-src";
              src = prev.lib.cleanSource
                (prev.nix-gitignore.gitignoreSourcePure [
                  ./.gitignore
                  ".github/"
                  "result*"
                  "nix/"
                  "*.nix"
                  "haskell-backend/src/main/native/haskell-backend/*"
                  "llvm-backend/src/main/native/llvm-backend/*"
                  "k-distribution/tests/regression-new"
                ] ./.);
              dontBuild = true;
              installPhase = ''
                mkdir $out
                cp -rv $src/* $out
                chmod -R u+w $out
                mkdir -p $out/llvm-backend/src/main/native/llvm-backend/matching
                cp -rv ${llvm-backend}/matching/* $out/llvm-backend/src/main/native/llvm-backend/matching
              '';
            };
            pythonOverrides = import ./pyk/nix/overlay.nix;
          in {
            inherit pythonOverrides;
            k = prev.callPackage ./nix/k.nix {
              inherit (prev) llvm-backend;
              mavenix = { inherit (prev) buildMaven; };
              haskell-backend = kore;
              inherit (haskell-backend) prelude-kore;
              inherit src;
              debugger = if prev.stdenv.isDarwin then
              # TODO lldb is broken on nixpkgs unstable, once the lldb support for 
              # k is done we should add lldb as runtime dependency here
                null
              else
                prev.gdb;
              version = "${k-version}-${self.rev or "dirty"}";
            };
          } // prev.lib.genAttrs [
            "python2"
            "python27"
            "python3"
            "python35"
            "python36"
            "python37"
            "python38"
            "python39"
            "python310"
          ] (python:
            prev.${python}.override {
              packageOverrides = pythonOverrides;
            }))
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
          overlays = [ (final: prev: { llvm-backend-release = false; }) ]
            ++ allOverlays;
        };
      in {

        packages = {
          inherit (pkgs) k;
          pyk = pkgs.python38Packages.pyk;

          update-maven = pkgs.writeShellScriptBin "update-maven" ''
            #!/bin/sh
            ${pkgs.nix}/bin/nix-build --no-out-link -E 'import ./nix/flake-compat-k-unwrapped.nix' \
              || echo "^~~~ expected error"

            ${pkgs.mavenix-cli}/bin/mvnix-update -l ./nix/mavenix.lock -E 'import ./nix/flake-compat-k-unwrapped.nix'
          '';

          update-python = pkgs.writeShellScriptBin "update-python" ''
            #!/bin/sh
            cd pyk
            ${
              pynixify.packages.${system}.pynixify
            }/bin/pynixify -l pyk --overlay-only --output ./nix
          '';

          check-versions = let
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
          in pkgs.writeShellScriptBin "check-versions" ''
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

          test = with pkgs;
            let
              k-version =
                lib.removeSuffix "\n" (builtins.readFile ./package/version);
            in stdenv.mkDerivation {
              name = "k-${k-version}-${self.rev or "dirty"}-test";
              src = lib.cleanSource
                (nix-gitignore.gitignoreSourcePure [ ./.gitignore ]
                  ./k-distribution);
              preferLocalBuild = true;
              buildInputs = [ gmp mpfr k ];
              postPatch = ''
                patchShebangs tests/regression-new/*
                substituteInPlace tests/regression-new/append/kparse-twice \
                  --replace '"$(dirname "$0")/../../../bin/kparse"' '"${k}/bin/kparse"'
                ${lib.optionalString stdenv.isDarwin ''
                  for mak in include/kframework/*.mak
                  do
                    substituteInPlace $mak \
                      --replace 'KOMPILE_FLAGS+=--no-exc-wrap' 'KOMPILE_FLAGS+=--no-exc-wrap --no-haskell-binary'
                  done
                ''}
              '';
              buildFlags = [
                "K_BIN=${k}/bin"
                "KLLVMLIB=${k}/lib/kllvm"
                "PACKAGE_VERSION=${k-version}"
                "--output-sync"
              ];
              enableParallelBuilding = true;
              preBuild = ''
                cd tests/regression-new
              '';
              installPhase = ''
                runHook preInstall
                touch "$out"
                runHook postInstall
              '';
            };

        };
        defaultPackage = pkgs.k;
      }) // {
        overlays.llvm-backend = llvm-backend.overlays.default;
        overlays.haskell-backend = haskell-backend.overlay;

        overlay = nixpkgs.lib.composeManyExtensions allOverlays;
      };
}
