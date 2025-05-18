{ src, maven, mvnHash, manualMvnArtifacts, manualMvnArtifactsJars, manualMvnSourceArtifacts, fileReplacements, clang, stdenv, lib, runCommand
, makeWrapper, bison, flex, gcc, git, gmp, jdk, jre, jre_minimal, mpfr, ncurses
, pkg-config, python3, python310, python311, z3, haskell-backend, prelude-kore, llvm-backend
, debugger, version, llvm-kompile-libs, runtimeShell }:

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
    pkg-config
    python3
    z3
    haskell-backend
    llvm-backend
  ] ++ lib.optional (debugger != null) debugger;
  runtimePath = lib.makeBinPath runtimeInputs;

  k = current-llvm-kompile-libs:
    maven.buildMavenPackage rec {
      pname = "k";
      inherit version src mvnHash manualMvnArtifacts manualMvnSourceArtifacts manualMvnArtifactsJars;

      buildOffline = true;

      mvnParameters =
        "-DskipTests -DskipKTest=true -Dllvm.backend.skip=true -Dhaskell.backend.skip=true -DsecondaryCacheDir=secondary-cache";

      nativeBuildInputs = [ makeWrapper ];

      postPatch = ''
        patchShebangs k-distribution/src/main/scripts/bin
        patchShebangs k-distribution/src/main/scripts/lib
      '';

      installPhase = ''
        mkdir -p $out/bin-unwrapped
        mkdir -p $out/bin

        cp scripts/k-which-python $out/bin
        substituteInPlace $out/bin/k-which-python \
          --replace "#!/usr/bin/env bash" "${runtimeShell}" \
          --replace "echo python3.10" "echo ${lib.makeBinPath [python310]}/python3" \
          --replace "echo python3.11" "echo ${lib.makeBinPath [python311]}/python3" \
          --replace "echo python3"    "echo ${lib.makeBinPath [python3]}/python3"

        cp -r k-distribution/target/release/k/bin/* $out/bin-unwrapped/
        cp -r k-distribution/target/release/k/{include,lib} $out/

        mkdir -p $out/lib/cmake/kframework
        cp ${llvm-backend.src}/cmake/* $out/lib/cmake/kframework/
        ln -sf ${llvm-backend}/include/kllvm $out/include/
        ln -sf ${llvm-backend}/include/kllvm-c $out/include/
        ln -sf ${llvm-backend}/lib/kllvm $out/lib/
        ln -sf ${llvm-backend}/lib/scripts $out/lib/

        ln -sf ${haskell-backend}/bin/kore-rpc $out/bin/kore-rpc
        ln -sf ${haskell-backend}/bin/kore-exec $out/bin/kore-exec
        ln -sf ${haskell-backend}/bin/kore-parser $out/bin/kore-parser
        ln -sf ${haskell-backend}/bin/kore-repl $out/bin/kore-repl
        ln -sf ${haskell-backend}/bin/kore-match-disjunction $out/bin/kore-match-disjunction

        ln -sf ${haskell-backend}/bin/kore-rpc-booster $out/bin/kore-rpc-booster
        ln -sf ${haskell-backend}/bin/kore-rpc-client $out/bin/kore-rpc-client
        ln -sf ${haskell-backend}/bin/booster-dev $out/bin/booster-dev

        prelude_kore="$out/include/kframework/kore/prelude.kore"
        mkdir -p "$(dirname "$prelude_kore")"
        ln -sf "${prelude-kore}" "$prelude_kore"

        for prog in $out/bin-unwrapped/*
        do
          makeWrapper $prog $out/bin/$(basename $prog) \
            --prefix PATH : ${runtimePath} ${
              lib.optionalString (current-llvm-kompile-libs != [ ]) ''
                --set NIX_LLVM_KOMPILE_LIBS "${
                  lib.strings.concatStringsSep " "
                  (lib.lists.sort (a: b: a < b) (lib.lists.unique current-llvm-kompile-libs))
                }"''
            }
        done

        ${if (current-llvm-kompile-libs == [ ]) then ''
          ln -sf ${llvm-backend}/bin/* $out/bin/
        '' else ''
          for prog in ${llvm-backend}/bin/*
          do
            makeWrapper $prog $out/bin/$(basename $prog) \
              --set NIX_LLVM_KOMPILE_LIBS "${
                lib.strings.concatStringsSep " "
                (lib.lists.sort (a: b: a < b) (lib.lists.unique current-llvm-kompile-libs))
              }"
          done''}
      '';

      preFixup = lib.optionalString (!stdenv.isDarwin) ''
        patchelf --set-interpreter "$(cat $NIX_CC/nix-support/dynamic-linker)" "$out/lib/kframework/bin/ng"
      '';

      passthru =
        builtins.mapAttrs (_: paths: k (current-llvm-kompile-libs ++ paths))
        llvm-kompile-libs // {
          inherit fileReplacements;
        };
    };
in k [ ]
