{ src, coreutils, darwin, clang, stdenv, lib, mavenix, runCommand, makeWrapper, bison, flex, gawk, gcc
, git, gmp, gnugrep, gnused, jdk, mpfr, ncurses, pkgconfig, python3, z3, haskell-backend
, prelude-kore, llvm-backend, debugger, version }:

let
  hostInputs = [
    coreutils
    gawk
    gnused
    bison
    flex
    (if stdenv.isDarwin then clang else gcc)
    gmp
    jdk
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

in mavenix.buildMaven {
    name = "k-${version}";
    infoFile = ./mavenix.lock;
    inherit src;
    nativeBuildInputs = [ makeWrapper ];

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
    # Finally we wrap all binaries with the required runtime deps
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
      ln -sf ${llvm-backend}/lib/kllvm $out/lib/
      ln -sf ${llvm-backend}/bin/* $out/bin/

      prelude_kore="$out/include/kframework/kore/prelude.kore"
      mkdir -p "$(dirname "$prelude_kore")"
      ln -sf "${prelude-kore}" "$prelude_kore"

      for prog in $out/bin/*
      do
        wrapProgram $prog --prefix PATH : ${hostPATH}
      done
    '';

    preFixup = lib.optionalString (!stdenv.isDarwin) ''
      patchelf --set-interpreter "$(cat $NIX_CC/nix-support/dynamic-linker)" "$out/bin/ng"
    '';

    doInstallCheck = true;
    installCheckPhase = ''
      $out/bin/ng --help
    '';
  }
