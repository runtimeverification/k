{
  description = "K Framework";
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-22.05";
    haskell-backend.url = "github:runtimeverification/haskell-backend";
    llvm-backend.url = "github:runtimeverification/llvm-backend";
    llvm-backend.inputs.nixpkgs.follows = "haskell-backend/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    rv-utils.url = "github:runtimeverification/rv-nix-tools";
    mavenix.url = "github:goodlyrottenapple/mavenix";
    # needed by nix/flake-compat-k-unwrapped.nix
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    poetry2nix.url = "github:nix-community/poetry2nix";
  };

  outputs = { self, nixpkgs, flake-utils, rv-utils, haskell-backend
    , llvm-backend, mavenix, flake-compat, poetry2nix }:
    let
      allOverlays = [
        poetry2nix.overlay
        mavenix.overlay
        llvm-backend.overlays.default
        haskell-backend.overlay # used only to override the z3 version to the same one as used by the haskell backend.
        (final: prev:
          let
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
          in {
            k-framework = haskell-backend-bins:
              prev.callPackage ./nix/k.nix {
                inherit (prev) llvm-backend;
                mavenix = { inherit (prev) buildMaven; };
                haskell-backend = haskell-backend-bins;
                inherit (haskell-backend) prelude-kore;
                inherit src;
                debugger = if prev.stdenv.isDarwin then
                # lldb is broken on this version of nixpkgs-unstable and there is no point including it
                # before the lldb support for k is added: https://github.com/runtimeverification/k/issues/2650
                  null
                else
                  prev.gdb;
                version = "${k-version}-${self.rev or "dirty"}";
              };

            pyk = prev.poetry2nix.mkPoetryApplication {
              python = prev.python39;
              projectDir = ./pyk;
              overrides = prev.poetry2nix.overrides.withDefaults
                (finalPython: prevPython: { kllvm = prev.kllvm; });
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
          overlays = [ (final: prev: { llvm-backend-release = false; }) ]
            ++ allOverlays;
        };

        haskell-backend-bins-version =
          haskell-backend.packages.${system}."kore:exe:kore-exec".version;
        haskell-backend-bins = pkgs.symlinkJoin {
          name = "kore-${haskell-backend-bins-version}-${
              haskell-backend.sourceInfo.shortRev or "local"
            }";
          paths = let p = haskell-backend.packages.${system};
          in [
            p."kore:exe:kore-exec"
            p."kore:exe:kore-rpc"
            p."kore:exe:kore-repl"
            p."kore:exe:kore-prof"
            p."kore:exe:kore-match-disjunction"
          ];
        };

      in rec {

        packages = rec {
          inherit (pkgs) pyk;
          k = pkgs.k-framework haskell-backend-bins;

          # This is a copy of the `nix/update-maven.sh` script, which should be
          # eventually removed. Having this inside the flake provides a uniform
          # interface, i.e. we have `update-maven`/`update-python` in k and 
          # `update-cabal` in the haskell-backend.
          # The first `nix-build` command below ensures k source is loaded into the Nix store. 
          # This command will fail, but only after loading the source. 
          # mavenix will not do this automatically because we it uses restrict-eval, 
          # and we are using filterSource, which is disabled under restrict-eval. 
          update-maven = pkgs.writeShellScriptBin "update-maven" ''
            #!/bin/sh
            ${pkgs.nix}/bin/nix-build --no-out-link -E 'import ./nix/flake-compat-k-unwrapped.nix' \
              || echo "^~~~ expected error"

            ${pkgs.mavenix-cli}/bin/mvnix-update -l ./nix/mavenix.lock -E 'import ./nix/flake-compat-k-unwrapped.nix'
          '';

          check-submodules = rv-utils.lib.check-submodules pkgs {
            inherit llvm-backend haskell-backend;
          };

          update-from-submodules =
            rv-utils.lib.update-from-submodules pkgs ./flake.lock {
              haskell-backend.submodule =
                "haskell-backend/src/main/native/haskell-backend";
              llvm-backend.submodule =
                "llvm-backend/src/main/native/llvm-backend";
            };

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
                ${
                # we add the `--no-haskell-binary` flag due to the compact library
                # (used to create the binary haskell files) being broken on Mac
                # https://github.com/runtimeverification/haskell-backend/issues/3137
                lib.optionalString stdenv.isDarwin ''
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
        defaultPackage = packages.k;
      }) // {
        overlays.llvm-backend = llvm-backend.overlays.default;
        overlays.z3 = haskell-backend.overlay;

        overlay = nixpkgs.lib.composeManyExtensions allOverlays;
      };
}
