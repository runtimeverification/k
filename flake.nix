{
  description = "K Framework";
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.05";
    haskell-backend.url = "github:runtimeverification/haskell-backend/03a6228f78d7f4805fee4b9d9c45208dcbe0c9fb";
    booster-backend = {
      url = "github:runtimeverification/hs-backend-booster/26b5d2df37c6fcc210d80ff57d1c3572a41f90b5";
      # NB booster-backend will bring in another dependency on haskell-backend,
      # but the two are not necessarily the same (different more often than not).
      # We get two transitive dependencies on haskell-nix.
      inputs.nixpkgs.follows = "haskell-backend/nixpkgs";
    };
    llvm-backend.url = "github:runtimeverification/llvm-backend";
    llvm-backend.inputs.nixpkgs.follows = "haskell-backend/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    rv-utils.url = "github:runtimeverification/rv-nix-tools";
    mavenix.url = "github:nix-community/mavenix";
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
        haskell-backend.overlays.z3
        haskell-backend.overlays.integration-tests
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
                clang = prev."clang_${toString final.llvm-version}";
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

        haskell-backend-bins = pkgs.symlinkJoin {
          name = "kore-${
              haskell-backend.sourceInfo.shortRev or "local"
            }";
          paths = let p = haskell-backend.packages.${system};
          in [
            p.kore-exec
            p.kore-match-disjunction
            p.kore-parser
            p.kore-repl
            p.kore-rpc
          ];
        };

      in rec {
        k-version = pkgs.lib.removeSuffix "\n" (builtins.readFile ./package/version);

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

          smoke-test = with pkgs;
            stdenv.mkDerivation {
              name = "k-${k-version}-${self.rev or "dirty"}-smoke-test";
              unpackPhase = "true";
              buildInputs = [ fmt gmp mpfr k ];
              buildPhase = ''
                echo "module TEST imports BOOL endmodule" > test.k
                kompile test.k --syntax-module TEST --backend llvm
                rm -rf test-kompiled
                kompile test.k --syntax-module TEST --backend haskell
              '';
              installPhase = ''
                runHook preInstall
                touch "$out"
                runHook postInstall
              '';
            };

          test = with pkgs;
            stdenv.mkDerivation {
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
        overlays.z3 = haskell-backend.overlays.z3;

        overlay = nixpkgs.lib.composeManyExtensions allOverlays;

      };
}
