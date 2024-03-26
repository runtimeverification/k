{
  description = "K Framework";
  inputs = {
    haskell-backend.url = "github:runtimeverification/haskell-backend/093af3153a5e07626d9b2e628d7ad4fc77c5a723";
    booster-backend = {
      url = "github:runtimeverification/hs-backend-booster/88ffab54a7266d8c98d5c039ef81143d1d24f3f0";
      inputs.nixpkgs.follows = "haskell-backend/nixpkgs";
      inputs.haskell-backend.follows = "haskell-backend";
      inputs.stacklock2nix.follows = "haskell-backend/stacklock2nix";
    };
    nixpkgs.follows = "llvm-backend/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    llvm-backend = {
      url = "github:runtimeverification/llvm-backend";
      inputs.utils.follows = "flake-utils";
    };
    rv-utils.url = "github:runtimeverification/rv-nix-tools";
  };

  outputs = { self, nixpkgs, flake-utils, rv-utils, haskell-backend
    , booster-backend, llvm-backend }:
    let
      allOverlays = [
        (_: _: {
          llvm-version = 15;
          llvm-backend-build-type = "Release";
        })
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
            # this version of maven from nixpkgs 23.11. we can remove this version of maven once our nixpkgs catches up
            maven = prev.callPackage ./nix/maven.nix { };

            k-framework = { haskell-backend-bins, llvm-kompile-libs }:
              prev.callPackage ./nix/k.nix {
                mvnHash = "sha256-8IJqbI5QFXTqR6QzMgsYG+STlXI93SzQkN+Xps10Zik=";
                manualMvnArtifacts = [
                  "org.scala-lang:scala-compiler:2.12.18"
                  "ant-contrib:ant-contrib:1.0b3"
                  "org.apache.ant:ant-nodeps:1.8.1"
                  "org.apache.maven.wagon:wagon-provider-api:1.0-alpha-6"
                ];
                manualMvnSourceArtifacts = [
                  "org.scala-sbt:compiler-bridge_2.12:1.8.0"
                ];
                inherit (final) maven;
                inherit (prev) llvm-backend;
                clang = prev."clang_${toString final.llvm-version}";
                booster =
                  booster-backend.packages.${prev.system}.kore-rpc-booster;
                rpc-client =
                  booster-backend.packages.${prev.system}.kore-rpc-client;
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
        pkgs = nixpkgs.lib.trivial.warnIf (llvm-backend.inputs.nixpkgs.rev
          != haskell-backend.inputs.nixpkgs.rev)
          "The version of nixpkgs in Haskell backend and LLVM backend has diverged!"
          import nixpkgs {
            inherit system;
            # Temporarily required until a bug on pyOpenSSL is resolved for aarch64-darwin
            # https://github.com/NixOS/nixpkgs/pull/172397
            config.allowBroken = system == "aarch64-darwin";
            overlays =
              [ (final: prev: { llvm-backend-build-type = "FastBuild"; }) ]
              ++ allOverlays;
          };

        haskell-backend-bins = pkgs.symlinkJoin {
          name = "kore-${haskell-backend.sourceInfo.shortRev or "local"}";
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
        k-version =
          pkgs.lib.removeSuffix "\n" (builtins.readFile ./package/version);

        packages = rec {
          k = pkgs.k-framework {
            inherit haskell-backend-bins;
            llvm-kompile-libs = with pkgs; {
              procps = [ "-I${procps}/include" "-L${procps}/lib" ];
              openssl = [ "-I${openssl.dev}/include" "-L${openssl.out}/lib" ];
              secp256k1 = [ "-I${secp256k1}/include" "-L${secp256k1}/lib" ];
            };
          };

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
              src = lib.cleanSource
                (nix-gitignore.gitignoreSourcePure [ ./.gitignore ]
                  ./k-distribution);
              preferLocalBuild = true;
              buildInputs = [ lsof fmt gmp mpfr k ];
              buildFlags = [
                "K_BIN=${k}/bin"
                "KLLVMLIB=${k}/lib/kllvm"
                "PACKAGE_VERSION=${k-version}"
                "--output-sync"
              ];
              enableParallelBuilding = true;
              preBuild = ''
                cd tests/smoke
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
        devShells.kore-integration-tests = pkgs.kore-tests (pkgs.k-framework {
          inherit haskell-backend-bins;
          llvm-kompile-libs = { };
        });
      }) // {
        overlays.llvm-backend = llvm-backend.overlays.default;
        overlays.z3 = haskell-backend.overlays.z3;

        overlay = nixpkgs.lib.composeManyExtensions allOverlays;

      };
}
