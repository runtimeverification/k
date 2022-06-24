{ src, clang, stdenv, lib, mavenix, runCommand, makeWrapper, bison, flex, gcc
, git, gmp, jdk, mpfr, ncurses, pkgconfig, python3, z3, haskell-backend
, prelude-kore, llvm-backend, debugger, version }:

let
  unwrapped = mavenix.buildMaven {
    name = "k-${version}-maven";
    infoFile = ./mavenix.lock;
    inherit src;

    # Cannot enable unit tests until a bug is fixed upstream (in Mavenix).
    doCheck = false;

    # Add build dependencies
    #
    nativeBuildInputs = [ makeWrapper ];

    buildInputs = [ clang flex gcc git gmp jdk mpfr pkgconfig python3 z3 ];

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

    # Make sure to link the cmake/ and include/ folders from the llvm-backend source repo and the llvm-backend derivation, 
    # as these may be expected/required when compiling other projects, e.g. the evm-semantics repo
    postInstall = ''
      cp -r k-distribution/target/release/k/{bin,include,lib} $out/
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
    clang
    gcc
    gmp
    jdk
    mpfr
    ncurses
    pkgconfig
    python3
    z3
    haskell-backend
    llvm-backend
  ] ++ lib.lists.optional (debugger != null) debugger;
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
