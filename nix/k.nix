{ src, clang, stdenv, lib, mavenix, runCommand, makeWrapper, bison, flex, gcc
, git, gmp, jdk, mpfr, ncurses, pkgconfig, python3, z3, haskell-backend
, prelude-kore, llvm-backend, debugger, version }:

let
  unwrapped = mavenix.buildMaven {
    name = "k-${version}-maven";
    infoFile = ./mavenix.lock;
    inherit src;

    # By default, mavenix copies the jars defined in `submodules` of mavenix.lock to `$out/share/java`.
    # The following flag disables this, since we copy the jars ourselves.
    # Otherwise, the jars are needlessly duplicated and bloat the cachix cache.
    copySubmodules = false;

    # Cannot enable unit tests until a bug is fixed upstream (in Mavenix).
    doCheck = false;

    # Add build dependencies
    #
    nativeBuildInputs = [ makeWrapper ];

    buildInputs = [ flex git gmp jdk mpfr pkgconfig python3 z3 ];

    # Set build environment variables
    #
    MAVEN_OPTS = [
      "-DskipKTest=true"
      "-Dllvm.backend.skip=true"
      "-Dhaskell.backend.skip=true"
    ];
    # Attributes are passed to the underlying `stdenv.mkDerivation`, so build
    #   hooks can be set here also.
    #
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
      ln -sf ${llvm-backend}/lib/kllvm $out/lib/
      ln -sf ${llvm-backend}/bin/* $out/bin/

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

in runCommand (lib.removeSuffix "-maven" unwrapped.name) {
  nativeBuildInputs = [ makeWrapper ];
  passthru = { inherit unwrapped; };
  inherit unwrapped;
} ''
  mkdir -p $out/bin

  # Wrap bin/ to augment PATH.
  for prog in $unwrapped/bin/*
  do
    makeWrapper $prog $out/bin/$(basename $prog) --prefix PATH : ${hostPATH}
  done

  # Link each top-level package directory, for dependents that need that.
  for each in include lib share
  do
    ln -sf $unwrapped/$each $out/$each
  done
''
