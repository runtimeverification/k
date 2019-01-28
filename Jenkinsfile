pipeline {
  agent {
    label 'docker'
  }
  stages {
    stage('Run in build environment') {
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          reuseNode true
        }
      }
      stages {
        stage("Init title") {
          when { changeRequest() }
          steps {
            script {
              currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}"
            }
          }
        }
        stage('Checkout code') {
          steps {
            dir('k-exercises') {
              git url: 'git@github.com:kframework/k-exercises.git'
            }
          }
        }
        stage('Build and Test K') {
          steps {
            ansiColor('xterm') {
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
        }
        stage('Build Debian Package') {
          steps {
            dir('kframework-5.0.0') {
              checkout scm
              sh '''
                . $HOME/.cargo/env
                dpkg-buildpackage
              '''
            }
            stash name: "bionic", includes: "kframework_5.0.0_amd64.deb"
          }
        }
      }
      post {
        always {
          sh 'k-distribution/target/release/k/bin/stop-kserver || true'
        }
      }
    }
    stage('Test Debian Package') {
      agent {
        docker {
          image 'ubuntu:bionic'
          args '-u 0'
        }
      }
      steps {
        unstash "bionic"
        sh '''
          apt-get update
          apt-get install -y ./kframework_5.0.0_amd64.deb
          cd /usr/lib/kframework
          echo 'Starting kserver...'
          bin/spawn-kserver kserver.log
          cd tutorial
          echo 'Testing tutorial in user environment...'
          make -j`nproc`
        '''
      }
      post {
        always {
          sh 'stop-kserver || true'
        }
      }
    }
    stage('Deploy') {
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          reuseNode true
        }
      }
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
        ansiColor('xterm') {
          dir("bionic") {
            unstash "bionic"
          }
          sh '''
            echo 'Setting up environment...'
            eval `opam config env`
            . $HOME/.cargo/env
            echo 'Deploying K...'
            mvn deploy -DskipKTest
            COMMIT=$(git rev-parse --short HEAD)
            DESCRIPTION='This is the nightly release of the K framework. To install, download and extract the \\"Prebuilt K binary\\", and follow the instructions in INSTALL.md within the target directory. On Windows, start by installing [Windows Subsystem for Linux](https://docs.microsoft.com/en-us/windows/wsl/install-win10) with Ubuntu, after which you can download and extract the archive by running:\\n```\\nsudo apt-get install wget\\nwget https://github.com/kframework/k/releases/download/nightly-'$COMMIT'/nightly.tar.gz\\ntar xvf nightly.tar.gz\\n```\\nfrom the bash terminal. K requires gcc and other Linux libraries to run, and building on native Windows, Cygwin, or MINGW is not supported.'
            RESPONSE=`curl --data '{"tag_name": "nightly-'$COMMIT'","name": "Nightly build of K framework at commit '$COMMIT'","body": "'"$DESCRIPTION"'", "draft": true,"prerelease": true}' https://api.github.com/repos/kframework/k/releases?access_token=$GITHUB_TOKEN`
            ID=`echo "$RESPONSE" | grep '"id": [0-9]*,' -o | head -1 | grep '[0-9]*' -o`
            curl --data-binary @k-distribution/target/k-nightly.tar.gz -H "Authorization: token $GITHUB_TOKEN" -H "Content-Type: application/gzip" https://uploads.github.com/repos/kframework/k/releases/$ID/assets?'name=nightly.tar.gz&label=Prebuilt+K+binary'
            curl --data-binary @bionic/kframework_5.0.0_amd64.deb -H "Authorization: token $GITHUB_TOKEN" -H "Content-Type: application/vnd.debian.binary-package" https://uploads.github.com/repos/kframework/k/releases/$ID/assets?'name=kframework_5.0.0_amd64.deb&label=Ubuntu+Bionic+Debian+Package'
            curl -X PATCH --data '{"draft": false}' https://api.github.com/repos/kframework/k/releases/$ID?access_token=$GITHUB_TOKEN
            curl --data '{"state": "success","target_url": "'$BUILD_URL'","description": "Build succeeded."}' https://api.github.com/repos/kframework/k/statuses/$(git rev-parse origin/master)?access_token=$GITHUB_TOKEN
          '''
        }
      }
    }
  }
}
