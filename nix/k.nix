{ src, clang, stdenv, lib, mavenix, runCommand, makeWrapper, bison, flex, gcc
, git, gmp, jdk, mpfr, ncurses, pkgconfig, python3, z3, haskell-backend
, prelude-kore, llvm-backend, debugger, version }:

let
  unwrapped = mavenix.buildMaven {
    name = "k-${version}";
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

    # Add extra maven dependencies which might not have been picked up
    #   automatically
    #
    #deps = [
    #  { path = "org/group-id/artifactId/version/file.jar"; sha1 = "0123456789abcdef"; }
    #  { path = "org/group-id/artifactId/version/file.pom"; sha1 = "123456789abcdef0"; }
    #];

    # Add dependencies on other mavenix derivations
    #
    #drvs = [ (import ../other/mavenix/derivation {}) ];

    # Override which maven package to build with
    #
    #maven = maven.overrideAttrs (_: { jdk = pkgs.oraclejdk10; });

    # Override remote repository URLs and settings.xml
    #
    #remotes = { central = "https://repo.maven.apache.org/maven2"; };
    #settings = ./settings.xml;
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
    debugger
  ];
  # PATH used at runtime
  hostPATH = lib.makeBinPath hostInputs;

in runCommand unwrapped.name {
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
