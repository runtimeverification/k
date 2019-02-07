pipeline {
  agent {
    label 'docker'
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
    stage('Build and Package K') {
      stages {
        stage('Build and Package on Ubuntu Bionic') {
          stages {
            stage('Build on Ubuntu Bionic') {
              agent {
                dockerfile {
                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg BASE_IMAGE=ubuntu:bionic'
                  reuseNode true
                }
              }
              stages {
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
                  reuseNode true
                }
              }
              options { skipDefaultCheckout() }
              steps {
                unstash "bionic"
                sh 'src/main/scripts/test-in-container'
              }
              post {
                always {
                  sh 'stop-kserver || true'
                }
              }
            }
          }
        }
        stage('Build and Package on Ubuntu Xenial') {
          when {
            anyOf {
              not { changeRequest() } 
              changelog '.*^\\[build-system\\] .+$'
              changeset 'Jenkinsfile'
              changeset 'Dockerfile'
            }
          }
          stages {
            stage('Build on Ubuntu Xenial') {
              agent {
                dockerfile {
                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg BASE_IMAGE=ubuntu:xenial'
                  reuseNode true
                }
              }
              stages {
                stage('Build Debian Package') {
                  steps {
                    dir('kframework-5.0.0') {
                      checkout scm
                      sh '''
                        . $HOME/.cargo/env
                        dpkg-buildpackage
                      '''
                    }
                    stash name: "xenial", includes: "kframework_5.0.0_amd64.deb"
                  }
                }
              }
            }
            stage('Test Debian Package') {
              agent {
                docker {
                  image 'ubuntu:xenial'
                  args '-u 0'
                  reuseNode true
                }
              }
              options { skipDefaultCheckout() }
              steps {
                unstash "xenial"
                sh 'src/main/scripts/test-in-container'
              }
              post {
                always {
                  sh 'stop-kserver || true'
                }
              }
            }
          }
        }
        stage('Build and Package on Debian Stretch') {
          when {
            anyOf {
              not { changeRequest() } 
              changelog '.*^\\[build-system\\] .+$'
              changeset 'Jenkinsfile'
              changeset 'Dockerfile'
            }
          }
          stages {
            stage('Build on Debian Stretch') {
              agent {
                dockerfile {
                  additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg BASE_IMAGE=debian:stretch'
                  reuseNode true
                }
              }
              stages {
                stage('Build Debian Package') {
                  steps {
                    dir('kframework-5.0.0') {
                      checkout scm
                      sh '''
                        . $HOME/.cargo/env
                        dpkg-buildpackage
                      '''
                    }
                    stash name: "stretch", includes: "kframework_5.0.0_amd64.deb"
                  }
                }
              }
            }
            stage('Test Debian Package') {
              agent {
                docker {
                  image 'debian:stretch'
                  args '-u 0'
                  reuseNode true
                }
              }
              options { skipDefaultCheckout() }
              steps {
                unstash "stretch"
                sh '''
                  echo "deb http://ftp.debian.org/debian stretch-backports main" > /etc/apt/sources.list.d/stretch-backports.list
                  src/main/scripts/test-in-container
                '''
              }
              post {
                always {
                  sh 'stop-kserver || true'
                }
              }
            }
          }
        }
      }
    }
    stage('Deploy') {
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg BASE_IMAGE=ubuntu:bionic'
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
          dir("xenial") {
            unstash "xenial"
          }
          dir("stretch") {
            unstash "stretch"
          }
          sh '''
            echo 'Setting up environment...'
            eval `opam config env`
            . $HOME/.cargo/env
            echo 'Deploying K...'
            mvn deploy -DskipKTest -Dcheckstyle.skip # TODO: fix checkstyle bug
            COMMIT=$(git rev-parse --short HEAD)
            DESCRIPTION='This is the nightly release of the K framework. To install, download the appropriate binary package and install using your package manager. You can install via `sudo apt-get install ./kframework_5.0.0_amd64_$ID.deb` for the appropriate version codename $ID. On Debian Stretch, you also must first enable stretch-backports by running `sudo echo \\"deb http://ftp.debian.org/debian stretch-backports main\\" > /etc/apt/sources.list.d/stretch-backports.list; sudo apt-get update`. If your OS is not supported, you can download and extract the \\"Platform-Independent K binary\\", and follow the instructions in INSTALL.md within the target directory. Note however that this will not support the Haskell or LLVM Backends. On Windows, start by installing [Windows Subsystem for Linux](https://docs.microsoft.com/en-us/windows/wsl/install-win10) with Ubuntu (or an Ubuntu VM), after which you can install like Ubuntu. K requires gcc and other Linux libraries to run, and building on native Windows, Cygwin, or MINGW is not supported.'
            RESPONSE=`curl --data '{"tag_name": "nightly-'$COMMIT'","name": "Nightly build of K framework at commit '$COMMIT'","body": "'"$DESCRIPTION"'", "draft": true,"prerelease": true}' https://api.github.com/repos/kframework/k/releases?access_token=$GITHUB_TOKEN`
            ID=`echo "$RESPONSE" | grep '"id": [0-9]*,' -o | head -1 | grep '[0-9]*' -o`
            curl --data-binary @k-distribution/target/k-nightly.tar.gz -H "Authorization: token $GITHUB_TOKEN" -H "Content-Type: application/gzip" https://uploads.github.com/repos/kframework/k/releases/$ID/assets?'name=nightly.tar.gz&label=Platform-Indepdendent+K+binary'
            curl --data-binary @bionic/kframework_5.0.0_amd64.deb -H "Authorization: token $GITHUB_TOKEN" -H "Content-Type: application/vnd.debian.binary-package" https://uploads.github.com/repos/kframework/k/releases/$ID/assets?'name=kframework_5.0.0_amd64_bionic.deb&label=Ubuntu+Bionic+Debian+Package'
            curl --data-binary @xenial/kframework_5.0.0_amd64.deb -H "Authorization: token $GITHUB_TOKEN" -H "Content-Type: application/vnd.debian.binary-package" https://uploads.github.com/repos/kframework/k/releases/$ID/assets?'name=kframework_5.0.0_amd64_xenial.deb&label=Ubuntu+Xenial+Debian+Package'
            curl --data-binary @stretch/kframework_5.0.0_amd64.deb -H "Authorization: token $GITHUB_TOKEN" -H "Content-Type: application/vnd.debian.binary-package" https://uploads.github.com/repos/kframework/k/releases/$ID/assets?'name=kframework_5.0.0_amd64_stretch.deb&label=Debian+Stretch+Debian+Package'
            curl -X PATCH --data '{"draft": false}' https://api.github.com/repos/kframework/k/releases/$ID?access_token=$GITHUB_TOKEN
            curl --data '{"state": "success","target_url": "'$BUILD_URL'","description": "Build succeeded."}' https://api.github.com/repos/kframework/k/statuses/$(git rev-parse origin/master)?access_token=$GITHUB_TOKEN
          '''
        }
      }
    }
  }
}
