{ src, maven, mvnHash, manualMvnArtifacts, clang, stdenv, lib, runCommand, makeWrapper, bison, flex, gcc, git
, gmp, jdk, jre, jre_minimal, mpfr, ncurses, pkgconfig, python3, z3
, haskell-backend, booster ? null, prelude-kore, llvm-backend, debugger, version
, llvm-kompile-libs }:

let
  runtimeInputs = [
    bison
    flex
    (if stdenv.isDarwin then clang else gcc)
    gmp
    (if stdenv.isDarwin && stdenv.isx86_64 then
      jre
    else
      (jre_minimal.override {
        modules = [ "java.base" "java.desktop" "java.logging" "java.rmi" ];
        jdk =
          if stdenv.isDarwin then jdk else jdk.override { headless = true; };
      }))
    mpfr
    ncurses
    pkgconfig
    python3
    z3
    haskell-backend
    llvm-backend
  ] ++ lib.optional (debugger != null) debugger;
  runtimePath = lib.makeBinPath runtimeInputs;
  k = current-llvm-kompile-libs:
    maven.buildMavenPackage rec {
      pname = "k";
      inherit version src mvnHash manualMvnArtifacts;

      buildOffline = true;

      mvnParameters =
        "-DskipTests -DskipKTest=true -Dllvm.backend.skip=true -Dhaskell.backend.skip=true -Dbooster.skip=true";
      nativeBuildInputs = [ makeWrapper ];

      preFixup = lib.optionalString (!stdenv.isDarwin) ''
        patchelf --set-interpreter "$(cat $NIX_CC/nix-support/dynamic-linker)" "$out/bin/ng"
      '';

      postPatch = ''
        patchShebangs k-distribution/src/main/scripts/bin
        patchShebangs k-distribution/src/main/scripts/lib
      '';

      installPhase = ''
        mkdir $out
        cp -r k-distribution/target/release/k/{bin,include,lib} $out/

        mkdir -p $out/lib/cmake/kframework && cp ${llvm-backend.src}/cmake/* $out/lib/cmake/kframework/
        ln -sf ${llvm-backend}/include/kllvm $out/include/
        ln -sf ${llvm-backend}/include/kllvm-c $out/include/
        ln -sf ${llvm-backend}/lib/kllvm $out/lib/
        ln -sf ${llvm-backend}/lib/scripts $out/lib/
        ln -sf ${llvm-backend}/bin/* $out/bin/

        ln -sf ${haskell-backend}/bin/kore-rpc $out/bin/kore-rpc
        ln -sf ${haskell-backend}/bin/kore-exec $out/bin/kore-exec
        ln -sf ${haskell-backend}/bin/kore-parser $out/bin/kore-parser
        ln -sf ${haskell-backend}/bin/kore-repl $out/bin/kore-repl
        ln -sf ${haskell-backend}/bin/kore-match-disjunction $out/bin/kore-match-disjunction

        ${lib.optionalString (booster != null)
        "ln -sf ${booster}/bin/* $out/bin/"}

        prelude_kore="$out/include/kframework/kore/prelude.kore"
        mkdir -p "$(dirname "$prelude_kore")"
        ln -sf "${prelude-kore}" "$prelude_kore"

        for prog in $out/bin/*
        do
          wrapProgram $prog \
            --prefix PATH : ${runtimePath} ${
              lib.optionalString (current-llvm-kompile-libs != [ ]) ''
                --set NIX_LLVM_KOMPILE_LIBS "${
                  lib.strings.concatStringsSep " "
                  (lib.lists.unique current-llvm-kompile-libs)
                }"''
            }
        done
      '';

      passthru =
        builtins.mapAttrs (_: paths: k (current-llvm-kompile-libs ++ paths))
        llvm-kompile-libs;
    };
in k [ ]
