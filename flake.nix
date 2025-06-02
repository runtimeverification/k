{
  description = "K Framework";
  inputs = {
    llvm-backend.url = "github:runtimeverification/llvm-backend/v0.1.132";
    haskell-backend = {
      url = "github:runtimeverification/haskell-backend/v0.1.126";
      inputs.rv-utils.follows = "llvm-backend/rv-utils";
      inputs.nixpkgs.follows = "llvm-backend/nixpkgs";
    };

    poetry2nix = {
      url = "github:nix-community/poetry2nix/2024.9.219347";
      inputs.nixpkgs.follows = "llvm-backend/nixpkgs";
    };

    nixpkgs.follows = "llvm-backend/nixpkgs";
    rv-utils.follows = "llvm-backend/rv-utils";
    flake-utils.follows = "llvm-backend/utils";
  };

  outputs = { self, nixpkgs, flake-utils, rv-utils, haskell-backend
    , llvm-backend, poetry2nix }:
    let
      allOverlays = [
        (_: _: {
          llvm-version = 17;
          llvm-backend-build-type = "Release";
        })

        llvm-backend.overlays.default

        haskell-backend.overlays.z3
        haskell-backend.overlays.integration-tests

        (import ./nix/pyk-overlay.nix {
          inherit poetry2nix;
          projectDir = ./pyk;
        })

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
                  # do not include submodule directories that might be initilized empty or non-existent
                  "/web/k-web-theme"
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

            haskell-backend-bins = prev.symlinkJoin {
              name = "kore-${haskell-backend.sourceInfo.shortRev or "local"}";
              paths = let p = haskell-backend.packages.${prev.system};
              in [
                p.kore-exec
                p.kore-match-disjunction
                p.kore-parser
                p.kore-repl
                p.kore-rpc
                p.kore-rpc-booster
                p.kore-rpc-client
                p.booster-dev
              ];
            };

            mk-k-framework = { haskell-backend-bins, llvm-kompile-libs }:
              prev.callPackage ./nix/k.nix {
                mvnHash = "sha256-aUomhCjSIBIQdavd3XojKJFdU74UURaKEVEKXiPTq1Q=";
                manualMvnArtifacts = [
                  "org.scala-lang:scala-compiler:2.13.13"
                  "ant-contrib:ant-contrib:1.0b3"
                  "org.apache.ant:ant-nodeps:1.8.1"
                  "org.apache.maven.wagon:wagon-provider-api:1.0-alpha-6"
                  "org.checkerframework:checker-qual:3.33.0"
                  "com.google.errorprone:error_prone_annotations:2.18.0"
                  "se.vandmo:dependency-lock-maven-plugin:1.2.2"
                ];
                manualMvnArtifactsJars = [
                  # e.g., this is basically se.vandmo:dependency-lock-maven-plugin:1.2.2:jar, but this way it works with `mvn dependency:get`
                  "se.vandmo:dependency-lock-maven-plugin:1.2.2"
                  "com.runtimeverification.k:k-frontend:1.0-SNAPSHOT"
                  "com.runtimeverification.k:llvm-backend-matching:1.0-SNAPSHOT"
                  "com.runtimeverification.k:llvm-backend:1.0-SNAPSHOT"
                  "com.runtimeverification.k:haskell-backend:1.0-SNAPSHOT"
                ];
                manualMvnSourceArtifacts =
                  [ "org.scala-sbt:compiler-bridge_2.13:1.8.0" ];
                fileReplacements = [
                  {
                    replace = "com/google/code/gson/gson/maven-metadata-central.xml";
                    replaceWith = ./nix/resources/maven-metadata-central-replacements/GSON.xml;
                    sha1 = "6761f9978777a91d499185a1516ea120f8f80a22";
                  }
                ];
                inherit (final) maven;
                inherit (prev) llvm-backend;
                clang = prev."clang_${toString final.llvm-version}";
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

            k = final.mk-k-framework {
              inherit (final) haskell-backend-bins;
              llvm-kompile-libs = with prev; {
                procps = [ "-I${procps}/include" "-L${procps}/lib" ];
                openssl = [ "-I${openssl.dev}/include" "-L${openssl.out}/lib" ];
                secp256k1 = [ "-I${secp256k1}/include" "-L${secp256k1}/lib" ];
              };
            };

            k-lock = final.k.overrideAttrs (finalAttrs: previousAttrs: {
              nativeBuildInputs = previousAttrs.nativeBuildInputs ++ (with final; [
                rsync
              ]);
              buildPhase = previousAttrs.buildPhase + ''
                echo "now running lock plugin offline"
                mvn -o -Dmaven.repo.local=.m2 se.vandmo:dependency-lock-maven-plugin:1.2.2:lock
              '';
              installPhase = previousAttrs.installPhase + ''
                mkdir -p $out/lock
                rsync -R dependencies-lock.json haskell-backend/dependencies-lock.json k-distribution/dependencies-lock.json k-frontend/dependencies-lock.json llvm-backend/dependencies-lock.json llvm-backend/src/main/native/llvm-backend/matching/dependencies-lock.json $out/lock/
              '';
            });
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

      in rec {
        k-version =
          pkgs.lib.removeSuffix "\n" (builtins.readFile ./package/version);

        packages = rec {
          inherit (pkgs) k k-lock pyk pyk-python310 pyk-python311 maven;

          check-submodules = rv-utils.lib.check-submodules pkgs {
            inherit llvm-backend haskell-backend;
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
        devShells.kore-integration-tests = pkgs.kore-tests
          (pkgs.mk-k-framework {
            inherit (pkgs) haskell-backend-bins;
            llvm-kompile-libs = { };
          });
      }) // {
        overlays.llvm-backend = llvm-backend.overlays.default;
        overlays.z3 = haskell-backend.overlays.z3;
        overlays.pyk = (import ./nix/pyk-overlay.nix {
          inherit poetry2nix;
          projectDir = ./pyk;
        });

        overlay = nixpkgs.lib.composeManyExtensions allOverlays;
      };
}
