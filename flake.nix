{
  description = "K Framework";
  inputs = {
    haskell-backend.url = "github:runtimeverification/haskell-backend";
    llvm-backend.url = "github:runtimeverification/llvm-backend";
    nixpkgs.follows = "haskell-backend/nixpkgs";
    llvm-backend.inputs.nixpkgs.follows = "haskell-backend/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    rv-utils.url = "github:runtimeverification/rv-nix-tools";
    mavenix.url = "github:goodlyrottenapple/mavenix";
    flake-compat = {
      url = "github:edolstra/flake-compat";
      flake = false;
    };
    pynixify.url = "github:goodlyrottenapple/pynixify";
  };

  outputs = { self, nixpkgs, flake-utils, rv-utils, haskell-backend, llvm-backend, mavenix
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
              # lldb is broken on this version of nixpkgs-unstable and there is no point including it
              # before the lldb support for k is added: https://github.com/runtimeverification/k/issues/2650
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
            prev.${python}.override { packageOverrides = pythonOverrides; }))
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

          update-python = pkgs.writeShellScriptBin "update-python" ''
            #!/bin/sh
            cd pyk
            ${
              pynixify.packages.${system}.pynixify
            }/bin/pynixify -l pyk --overlay-only --output ./nix
          '';

          check-submodules = rv-utils.lib.check-submodules pkgs {
            inherit llvm-backend haskell-backend;
          };
          
          update-from-submodules = rv-utils.lib.update-from-submodules pkgs ./flake.lock {
            haskell-backend.submodule = "haskell-backend/src/main/native/haskell-backend";
            llvm-backend.submodule = "llvm-backend/src/main/native/llvm-backend";
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
        defaultPackage = pkgs.k;
      }) // {
        overlays.llvm-backend = llvm-backend.overlays.default;
        overlays.haskell-backend = haskell-backend.overlay;

        overlay = nixpkgs.lib.composeManyExtensions allOverlays;
      };
}
