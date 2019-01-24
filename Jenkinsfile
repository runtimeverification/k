pipeline {
  agent {
    docker {
      image 'ubuntu:bionic'
      args '-u 0'
    }
  }
  options {
    skipDefaultCheckout true
  }
  stages {
    stage('Checkout code') {
      steps {
        sh 'rm -rf ./*'
        checkout scm
        dir('k-exercises') {
          git url: 'git@github.com:kframework/k-exercises.git'
        }
      }
    }
    stage('Install dependencies') {
      steps {
        sh '''
          apt-get update
          apt-get install -y git debhelper maven openjdk-8-jdk cmake libboost-test-dev libyaml-cpp-dev libjemalloc-dev flex bison clang-6.0 zlib1g-dev libgmp-dev libmpfr-dev gcc z3 libz3-dev opam pkg-config curl
          k-distribution/src/main/scripts/bin/k-configure-opam-dev
          curl https://sh.rustup.rs -sSf | sh -s -- -y
          . $HOME/.cargo/env
          rustup toolchain install 1.28.0
          rustup default 1.28.0
          curl -sSL https://get.haskellstack.org/ | sh      
          mkdir -p ~/.stack
          echo 'allow-different-user: true' > ~/.stack/config.yaml
        '''
      }
    }
    stage('Build and Test') {
      steps {
        sh '''
          echo 'Setting up environment...'
          eval `opam config env`
          . $HOME/.cargo/env
          echo 'Building K...'
          mvn verify -U
          echo 'Starting kserver...'
          k-distribution/target/release/k/bin/spawn-kserver kserver.log
          cd k-exercises/tutorial
          make -j`nproc`
        '''
      }
    }
    stage('Deploy') {
      when { 
        not { changeRequest() }
        branch 'master'
      }
      environment {
        AWS_ACCESS_KEY_ID = credentials('aws-access-key-id')
        AWS_SECRET_ACCESS_KEY = credentials('aws-secret-access-key')
        AWS_REGION='us-east-2'
        GITHUB_TOKEN = credentials('rv-jenkins')
      }
      steps {
       sh '''
          mvn deploy -DskipKTest
          COMMIT=$(git rev-parse --short HEAD)
          DESCRIPTION='This is the nightly release of the K framework. To install, download and extract the \"Prebuilt K binary\", and follow the instructions in INSTALL.md within the target directory. On Windows, start by installing [Windows Subsystem for Linux](https://docs.microsoft.com/en-us/windows/wsl/install-win10) with Ubuntu, after which you can download and extract the archive by running:\n```\nsudo apt-get install wget\nwget https://github.com/kframework/k/releases/download/nightly-'$COMMIT'/nightly.tar.gz\ntar xvf nightly.tar.gz\n```\nfrom the bash terminal. K requires gcc and other Linux libraries to run, and building on native Windows, Cygwin, or MINGW is not supported.'
          RESPONSE=`curl --data '{"tag_name": "nightly-'$COMMIT'","name": "Nightly build of K framework at commit '$COMMIT'","body": "'"$DESCRIPTION"'", "draft": true,"prerelease": true}' https://api.github.com/repos/kframework/k/releases?access_token=$GITHUB_TOKEN`
          ID=`echo "$RESPONSE" | grep '"id": [0-9]*,' -o | head -1 | grep '[0-9]*' -o`
          curl --data-binary @k-distribution/target/k-nightly.tar.gz -H "Authorization: token $GITHUB_TOKEN" -H "Content-Type: application/gzip" https://uploads.github.com/repos/kframework/k/releases/$ID/assets?'name=nightly.tar.gz&label=Prebuilt+K+binary'
          curl -X PATCH --data '{"draft": false}' https://api.github.com/repos/kframework/k/releases/$ID?access_token=$GITHUB_TOKEN
          curl --data '{"state": "success","target_url": "'$BUILD_URL'","description": "Build succeeded."}' https://api.github.com/repos/kframework/k/statuses/$(git rev-parse origin/master)?access_token=$GITHUB_TOKEN
        '''
      }
    }
  }
  post {
    always {
      sh 'k-distribution/target/release/k/bin/stop-kserver || true'
    }
  }
}
