{ stdenv, lib, mavenix, cleanGit, cleanSourceWith, runCommand, makeWrapper
, bison, flex, gcc, git, gmp, jdk, mpfr, ncurses, pkgconfig, python3, z3
, haskell-backend, prelude-kore, llvm-backend
}:

let
  unwrapped = mavenix.buildMaven {
    name = "k-5.1.210";
    infoFile = ./mavenix.lock;
    src =
      cleanSourceWith {
        name = "k";
        src = cleanGit { src = ./..; name = "k"; };
        ignore =
          [
            "result*" "nix/" "*.nix"
            "haskell-backend/src/main/native/haskell-backend/*"
            "llvm-backend/src/main/native/llvm-backend/*"
            "!llvm-backend/src/main/native/llvm-backend/matching"  # need pom.xml
            "k-distribution/tests/regression-new"
          ];
      };

    # Cannot enable unit tests until a bug is fixed upstream (in Mavenix).
    doCheck = false;

    # Add build dependencies
    #
    nativeBuildInputs = [ makeWrapper ];

    buildInputs = [ flex gcc git gmp jdk mpfr pkgconfig python3 z3 ];

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

    postInstall = ''
      cp -r k-distribution/target/release/k/{bin,include,lib} $out/

      rm "$out/bin/k-configure-opam"
      rm "$out/bin/k-configure-opam-dev"
      rm "$out/bin/kserver-opam"
      rm -fr "$out/lib/opam"

      prelude_kore="$out/include/kframework/kore/prelude.kore"
      mkdir -p "$(dirname "$prelude_kore")"
      ln -s "${prelude-kore}" "$prelude_kore"
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
in

let
  hostInputs = [
    bison flex gcc gmp jdk mpfr ncurses pkgconfig python3 z3
    haskell-backend llvm-backend
  ];
  # PATH used at runtime
  hostPATH = lib.makeBinPath hostInputs;
in

runCommand unwrapped.name
  {
    nativeBuildInputs = [ makeWrapper ];
    passthru = { inherit unwrapped; };
    inherit unwrapped;
  }
  ''
    mkdir -p $out/bin

    # Wrap bin/ to augment PATH.
    for prog in $unwrapped/bin/*
    do
      makeWrapper $prog $out/bin/$(basename $prog) --prefix PATH : ${hostPATH}
    done

    # Link each top-level package directory, for dependents that need that.
    for each in include lib share
    do
      ln -s $unwrapped/$each $out/$each
    done
  ''
