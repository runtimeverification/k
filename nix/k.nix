{ src, clang, stdenv, lib, mavenix, runCommand, makeWrapper, bison, flex, gcc
, git, gmp, jdk, jre_minimal, mpfr, ncurses, pkgconfig, python3, z3
, haskell-backend, booster ? null, prelude-kore, llvm-backend, debugger, version
, llvm-kompile-libs }:

let
  unwrapped = mavenix.buildMaven {
    name = "k-${version}-maven";
    infoFile = ./mavenix.lock;
    inherit src;

    # By default, mavenix copies the jars defined in `submodules` of mavenix.lock to `$out/share/java`.
    # The following flag disables this, since we copy the jars ourselves.
    # Otherwise, the jars are needlessly duplicated and bloat the cachix cache.
    copySubmodules = false;

    # Add build dependencies
    buildInputs = [ git ];

    # Set build environment variables
    MAVEN_OPTS = [
      "-DskipKTest=true"
      "-Dllvm.backend.skip=true"
      "-Dhaskell.backend.skip=true"
      "-Dbooster.skip=true"
    ];
    # Attributes are passed to the underlying `stdenv.mkDerivation`, so build
    # hooks can also be set here.
    postPatch = ''
      patchShebangs k-distribution/src/main/scripts/bin
      patchShebangs k-distribution/src/main/scripts/lib
    '';

    # We first copy the bin, include and lib folders from the build and then replace all copied jars which already exist
    # in $out/share/mavenix/repo with a symlink to reduce the derivation size. This is done to reduce the cachix upload sizes
    # We also have to make sure to link the cmake/ and include/ folders from the llvm-backend source repo and the llvm-backend derivation, 
    # as these will be expected/required when compiling other projects, e.g. the evm-semantics repo
    postInstall = ''
      cp -r k-distribution/target/release/k/{bin,include,lib} $out/

      for file in $out/lib/kframework/java/*; do
        file_name=$(basename $file)
        found_in_share="$(find -L $out/share/mavenix/repo -maxdepth 20 -name "$file_name")"
        if [ ! -z "$found_in_share" ]; then
          rm "$file"
          ln -sf "$found_in_share" "$file"
        fi
      done

      mkdir -p $out/lib/cmake/kframework && ln -sf ${llvm-backend.src}/cmake/* $out/lib/cmake/kframework/
      ln -sf ${llvm-backend}/include/kllvm $out/include/
      ln -sf ${llvm-backend}/include/kllvm-c $out/include/
      ln -sf ${llvm-backend}/lib/kllvm $out/lib/
      ln -sf ${llvm-backend}/lib/scripts $out/lib/
      ln -sf ${llvm-backend}/bin/* $out/bin/
      ${lib.optionalString (booster != null)
      "ln -sf ${booster}/bin/* $out/bin/"}

      prelude_kore="$out/include/kframework/kore/prelude.kore"
      mkdir -p "$(dirname "$prelude_kore")"
      ln -sf "${prelude-kore}" "$prelude_kore"
    '';

    preFixup = lib.optionalString (!stdenv.isDarwin) ''
      patchelf --set-interpreter "$(cat $NIX_CC/nix-support/dynamic-linker)" "$out/bin/ng"
    '';

    doInstallCheck = true;
    installCheckPhase = ''
      $out/bin/ng --help
    '';
  };

in let
  hostInputs = [
    bison
    flex
    (if stdenv.isDarwin then clang else gcc)
    gmp
    (if stdenv.isDarwin then jre_minimal else jre_minimal.override { jdk = jdk.override { headless = true; }; })
    mpfr
    ncurses
    pkgconfig
    python3
    z3
    haskell-backend
    llvm-backend
  ] ++ lib.optional (debugger != null) debugger;
  # PATH used at runtime
  hostPATH = lib.makeBinPath hostInputs;

  final = current-llvm-kompile-libs:
    runCommand (lib.removeSuffix "-maven" unwrapped.name) {
      nativeBuildInputs = [ makeWrapper ];
      passthru = {
        inherit unwrapped;
      } // builtins.mapAttrs
        (_: paths: final (current-llvm-kompile-libs ++ paths))
        llvm-kompile-libs;
      inherit unwrapped;
    } ''
      mkdir -p $out/bin

      # Wrap bin/ to augment PATH.
      for prog in $unwrapped/bin/*
      do
        makeWrapper $prog $out/bin/$(basename $prog) \
          --prefix PATH : ${hostPATH} ${
            lib.optionalString (current-llvm-kompile-libs != [ ]) ''
              --set NIX_LLVM_KOMPILE_LIBS "${
                lib.strings.concatStringsSep " "
                (lib.lists.unique current-llvm-kompile-libs)
              }"''
          }
      done

      # Link each top-level package directory, for dependents that need that.
      for each in include lib share
      do
        ln -sf $unwrapped/$each $out/$each
      done

      ln -sf ${haskell-backend}/bin/kore-rpc $out/bin/kore-rpc
      ln -sf ${haskell-backend}/bin/kore-exec $out/bin/kore-exec
      ln -sf ${haskell-backend}/bin/kore-parser $out/bin/kore-parser
      ln -sf ${haskell-backend}/bin/kore-repl $out/bin/kore-repl
      ln -sf ${haskell-backend}/bin/kore-match-disjunction $out/bin/kore-match-disjunction
    '';
in final [ ]
