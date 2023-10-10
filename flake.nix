{
  description = "K Framework";
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.05";
    haskell-backend.url = "github:runtimeverification/haskell-backend/63397c713d21322434d572281c1407d929a1189e";
    booster-backend = {
      url = "github:runtimeverification/hs-backend-booster/6c2f5ab988e2c5f98b1cdeb04b8a5787d8a7c566";
      # NB booster-backend will bring in another dependency on haskell-backend,
      # but the two are not necessarily the same (different more often than not).
      # We get two transitive dependencies on haskell-nix.
      inputs.nixpkgs.follows = "haskell-backend/nixpkgs";
    };
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
  };

  outputs = { self, nixpkgs, flake-utils, rv-utils, haskell-backend, booster-backend
    , llvm-backend, mavenix, flake-compat }:
    let
      allOverlays = [
        (_: _: {
          llvm-version = 13;
          llvm-backend-build-type = "Release"; })
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
                  "hs-backend-booster/src/main/native/hs-backend-booster/*"
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
            k-framework = { haskell-backend-bins, llvm-kompile-libs }:
              prev.callPackage ./nix/k.nix {
                inherit (prev) llvm-backend;
                booster = booster-backend.packages.${prev.system}.kore-rpc-booster;
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
                inherit llvm-kompile-libs;
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

          # Temporarily required until a bug on pyOpenSSL is resolved for aarch64-darwin
          # https://github.com/NixOS/nixpkgs/pull/172397
          config.allowBroken = system == "aarch64-darwin";
          overlays = [ (final: prev: { llvm-backend-build-type = "FastBuild"; }) ]
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
            p."kore:exe:kore-parser"
            p."kore:exe:kore-match-disjunction"
          ];
        };

      in rec {

        packages = rec {
          k = pkgs.k-framework {
            inherit haskell-backend-bins;
            llvm-kompile-libs = with pkgs; {
              procps = [ "-I${procps}/include" "-L${procps}/lib" ];
              openssl = [ "-I${openssl.dev}/include" "-L${openssl.out}/lib" ];
            };
          };

          # This is a copy of the `nix/update-maven.sh` script, which should be
          # eventually removed. Having this inside the flake provides a uniform
          # interface, i.e. we have `update-maven` in k and
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
            inherit llvm-backend haskell-backend booster-backend;
          };

          update-from-submodules =
            rv-utils.lib.update-from-submodules pkgs ./flake.lock {
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
              buildInputs = [ fmt gmp mpfr k ];
              postPatch = ''
                patchShebangs tests/regression-new/*
                substituteInPlace tests/regression-new/append/kparse-twice \
                  --replace '"$(dirname "$0")/../../../bin/kparse"' '"${k}/bin/kparse"'
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
        devShells.kore-integration-tests = pkgs.kore-tests (pkgs.k-framework { inherit haskell-backend-bins; llvm-kompile-libs = {}; });
      }) // {
        overlays.llvm-backend = llvm-backend.overlays.default;
        overlays.z3 = haskell-backend.overlay;

        overlay = nixpkgs.lib.composeManyExtensions allOverlays;

      };
}
