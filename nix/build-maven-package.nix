{ lib, stdenv, maven }:

{ src, sourceRoot ? null, buildOffline ? false, patches ? [ ], pname, version
, mvnHash ? "", mvnFetchExtraArgs ? { }, mvnDepsParameters ? ""
, manualMvnArtifacts ? [ ], manualMvnArtifactsJars ? [ ], manualMvnSourceArtifacts ? [ ]
, mvnParameters ? "", passthru, ... }@args:

# originally extracted from dbeaver
# created to allow using maven packages in the same style as rust

let
  doReplacement = replacement: [ ''
    REPLACE_PATH=.m2/${replacement.replace}
    echo "copying ${replacement.replaceWith} to maven repository"
    mkdir -p $(dirname $REPLACE_PATH)
    cp ${replacement.replaceWith} $REPLACE_PATH
    echo ${replacement.sha1} > $REPLACE_PATH.sha1
  '' ];
  fetchedMavenDeps = stdenv.mkDerivation ({
    name = "${pname}-${version}-maven-deps";
    inherit src sourceRoot patches;

    nativeBuildInputs = [ maven ];

    buildPhase = ''
      runHook preBuild
    '' + lib.optionalString buildOffline ''
      mvn org.apache.maven.plugins:maven-dependency-plugin:3.6.1:go-offline -Dmaven.repo.local=$out/.m2 ${mvnDepsParameters}

      for artifactId in ${builtins.toString manualMvnArtifacts}
      do
        echo "downloading manual $artifactId"
        mvn dependency:get -Dartifact="$artifactId" -Dmaven.repo.local=$out/.m2
      done

      for artifact in ${builtins.toString manualMvnArtifactsJars}
      do
        groupId=$(echo $artifact | cut -d':' -f1)
        artifactId=$(echo $artifact | cut -d':' -f2)
        version=$(echo $artifact | cut -d':' -f3)
        echo "downloading manual jar $artifactId"
        mvn dependency:get -DgroupId=$groupId -DartifactId=$artifactId -Dversion=$version -Dmaven.repo.local=$out/.m2
      done 

      for artifact in ${builtins.toString manualMvnSourceArtifacts}
      do
        groupId=$(echo $artifact | cut -d':' -f1)
        artifactId=$(echo $artifact | cut -d':' -f2)
        version=$(echo $artifact | cut -d':' -f3)
        echo "downloading manual sources $artifactId"
        mvn dependency:get -Dclassifier=sources -DgroupId=$groupId -DartifactId=$artifactId -Dversion=$version -Dmaven.repo.local=$out/.m2
      done
    '' + lib.optionalString (!buildOffline) ''
      mvn package -Dmaven.repo.local=$out/.m2 ${mvnParameters}
    '' + ''
      runHook postBuild
    '';

    # keep only *.{pom,jar,sha1,nbm} and delete all ephemeral files with lastModified timestamps inside
    installPhase = ''
      runHook preInstall

      # removing maven-metadata-central.xml might require replicable substitutes in rare cases, see e.g. GSON
      find $out -type f \( \
        -name \*.lastUpdated \
        -o -name resolver-status.properties \
        -o -name _remote.repositories \
        -o -name \*.snapshots.xml \
        -o -name \*.snapshots.xml.sha1 \
        -o -name maven-metadata-central.xml \
        -o -name maven-metadata-central.xml.sha1 \) \
        -delete
      
      # delete any empty directories
      find . -type d -empty -delete

      runHook postInstall
    '';

    # don't do any fixup
    dontFixup = true;
    outputHashAlgo = if mvnHash != "" then null else "sha256";
    outputHashMode = "recursive";
    outputHash = mvnHash;
  } // mvnFetchExtraArgs);
in stdenv.mkDerivation (builtins.removeAttrs args [ "mvnFetchExtraArgs" ] // {
  inherit fetchedMavenDeps;

  nativeBuildInputs = args.nativeBuildInputs or [ ] ++ [ maven ];

  buildPhase = ''
    runHook preBuild

    mvnDeps=$(cp -dpR ${fetchedMavenDeps}/.m2 ./ && chmod +w -R .m2 && pwd)

    # replace/add additional replicable build files
    '' + lib.strings.concatStringsSep "\n" (builtins.concatMap doReplacement passthru.fileReplacements) + ''
    chmod +w -R .m2

    mvn package -o -nsu "-Dmaven.repo.local=$mvnDeps/.m2" ${mvnParameters}

    runHook postBuild
  '';

  meta = args.meta or { } // {
    platforms = args.meta.platforms or maven.meta.platforms;
  };
})
