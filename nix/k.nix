{ lib, mavenix, nix-gitignore, makeWrapper
, flex, gcc, git, gmp, jdk, mpfr, pkgconfig, python3, z3
}:

let inherit (nix-gitignore) gitignoreRecursiveSource; in

let
  hostInputs = [ flex gcc gmp jdk mpfr pkgconfig python3 z3 ];
  # PATH used at runtime
  hostPATH = lib.makeBinPath hostInputs;
in

mavenix.buildMaven {
  name = "k-5.0.0";
  infoFile = ./mavenix.lock;
  doCheck = false;
  src = gitignoreRecursiveSource [ "nix/" "*.nix" ] ./..;

  # Add build dependencies
  #
  nativeBuildInputs = [ makeWrapper ];

  buildInputs =
    [ git ]
    ++ hostInputs;

  # Set build environment variables
  #
  MAVEN_OPTS = [
    "-DskipTests=true"
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

    for prog in $out/bin/*; do
      wrapProgram $prog --prefix PATH : ${hostPATH}
    done
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
}
