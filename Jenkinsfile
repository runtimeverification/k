pipeline {
  agent { label 'docker' }
  options { ansiColor('xterm') }
  environment {
    PACKAGE         = 'kframework'
    ROOT_URL        = 'https://github.com/runtimeverification/k/releases/download'
    SHORT_REV       = """${sh(returnStdout: true, script: 'git rev-parse --short=7 HEAD').trim()}"""
    LONG_REV        = """${sh(returnStdout: true, script: 'git rev-parse HEAD').trim()}"""
    VERSION         = """${sh(returnStdout: true, script: 'cat package/version').trim()}"""
    K_RELEASE_TAG   = "v${env.VERSION}"
    MAKE_EXTRA_ARGS = '' // Example: 'DEBUG=--debug' to see stack traces
  }
  stages {
    stage('Create source tarball') {
      when {
        branch 'master'
        beforeAgent true
      }
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          reuseNode true
        }
      }
      steps {
        dir("kframework-${env.VERSION}") {
          checkout scm
          sh '''
            find . -name .git | xargs rm -r
            cd ..
            tar czvf kframework-${VERSION}-src.tar.gz kframework-${VERSION}
          '''
          deleteDir()
        }
        stash name: 'src', includes: "kframework-${env.VERSION}-src.tar.gz"
      }
    }
    stage('Build and Package on Arch Linux') {
      when {
        branch 'master'
        beforeAgent true
      }
      stages {
        stage('Build on Arch Linux') {
          agent {
            dockerfile {
              filename 'package/arch/Dockerfile'
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
              reuseNode true
            }
          }
          stages {
            stage('Build Pacman Package') {
              steps {
                dir("kframework-arch-${env.VERSION}") {
                  checkout scm
                  sh '''
                    mv package/arch/* ./
                    makepkg
                  '''
                  stash name: 'arch', includes: "kframework-git-${env.VERSION}-1-x86_64.pkg.tar.zst"
                }
              }
            }
          }
        }
        stage('Test Arch Package') {
          agent {
            docker {
              image 'archlinux:base'
              args '-u 0'
              reuseNode true
            }
          }
          options { skipDefaultCheckout() }
          steps {
            unstash 'arch'
            sh '''
              pacman -Syyu --noconfirm
              pacman -U --noconfirm kframework-git-${VERSION}-1-x86_64.pkg.tar.zst
              src/main/scripts/test-in-container
            '''
          }
          post {
            always {
              sh 'stop-kserver || true'
              archiveArtifacts 'kserver.log,k-distribution/target/kserver.log'
            }
          }
        }
      }
      post {
        failure {
          slackSend color: '#cb2431'                                         \
                  , channel: '#k'                                            \
                  , message: "Arch Linux Packaging Failed: ${env.BUILD_URL}"
        }
      }
    }
    stage('Deploy') {
      when {
        branch 'master'
        beforeAgent true
      }
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          reuseNode true
        }
      }
      post { failure { slackSend color: '#cb2431' , channel: '#k' , message: "Deploy Phase Failed: ${env.BUILD_URL}" } }
      environment { GITHUB_TOKEN = credentials('rv-jenkins-access-token') }
      steps {
        unstash 'src'
        dir('arch')     { unstash 'arch'     }
        sshagent(['rv-jenkins-github']) {
          sh '''
            git clone 'ssh://github.com/runtimeverification/k.git' k-release
            cd k-release
            git fetch --all

            release_commit="$LONG_REV"
            git checkout ${release_commit}

            git tag -d "${K_RELEASE_TAG}"         || true
            git push -d origin "${K_RELEASE_TAG}" || true
            hub release delete "${K_RELEASE_TAG}" || true

            git tag "${K_RELEASE_TAG}" "${release_commit}"
            git push origin "${K_RELEASE_TAG}"

            mv ../kframework-${VERSION}-src.tar.gz                     kframework-${VERSION}-src.tar.gz
            mv ../arch/kframework-git-${VERSION}-1-x86_64.pkg.tar.zst  kframework-git-${VERSION}-1-x86_64.pkg.tar.zst

            echo "K Framework Release ${VERSION}"  > release.md
            echo ''                               >> release.md
            cat k-distribution/INSTALL.md         >> release.md
            hub release create --prerelease                                                      \
                --attach kframework-${VERSION}-src.tar.gz'#Source tar.gz'                        \
                --attach kframework-git-${VERSION}-1-x86_64.pkg.tar.zst'#Arch Package'           \
                --file release.md "${K_RELEASE_TAG}"
          '''
        }
      }
    }
  }
}
