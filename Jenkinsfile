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
    stage('Init title') {
      when { changeRequest() }
      steps {
        script { currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}" }
        milestone(1)
      }
    }
    stage('Create source tarball') {
      when {
        anyOf {
          branch 'release'
          changeRequest()
        }
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
    stage('Build and Package on Ubuntu Focal') {
      when {
        anyOf {
          branch 'release'
          changeRequest()
        }
        beforeAgent true
      }
      stages {
        stage('Build on Ubuntu Focal') {
          agent {
            dockerfile {
              filename 'package/debian/Dockerfile'
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg LLVM_VERSION=12'
              reuseNode true
            }
          }
          stages {
            stage('Checkout code') { steps { dir('k-exercises') { git url: 'git@github.com:kframework/k-exercises.git', credentialsId: 'rv-jenkins-access-token' } } }
            stage('Build and Test K') {
              options { timeout(time: 45, unit: 'MINUTES') }
              steps {
                sh '''
                  echo 'Setting up environment...'
                  export K_OPTS='-Xmx12G'
                  echo 'Building K...'
                  mvn --batch-mode verify -U
                  echo 'Testing pyk...'
                  make -C pyk all
                  echo 'Starting kserver...'
                  k-distribution/target/release/k/bin/spawn-kserver kserver.log
                  cd k-exercises/tutorial
                  make -j`nproc` --output-sync ${MAKE_EXTRA_ARGS}
                  cd ../../k-distribution/k-tutorial/1_basic
                  ./test_kompile.sh
                '''
              }
              post {
                always {
                  sh 'k-distribution/target/release/k/bin/stop-kserver || true'
                  archiveArtifacts 'kserver.log,k-distribution/target/kserver.log'
                }
              }
            }
            stage('Build Debian Package') {
              steps {
                dir("kframework-${env.VERSION}") {
                  checkout scm
                  sh '''
                    mv package/debian ./debian
                    mv debian/control.focal debian/control
                    dpkg-buildpackage
                  '''
                }
                stash name: 'focal', includes: "kframework_${env.VERSION}_amd64.deb"
              }
            }
          }
          post {
            always {
              sh '''
                rm -rf k-distribution/k-tutorial/1_basic/build
                make --directory=k-distribution clean
                make --directory=k-exercises clean
                make --directory=haskell-backend/src/main/native/haskell-backend clean
              '''
            }
          }
        }
        stage('Test Debian Package') {
          agent {
            docker {
              image 'ubuntu:focal'
              args '-u 0'
              reuseNode true
            }
          }
          options { skipDefaultCheckout() }
          steps {
            unstash 'focal'
            sh 'src/main/scripts/test-in-container-debian'
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
          slackSend color: '#cb2431'                                             \
                  , channel: '#k'                                                \
                  , message: "Ubuntu Focal Packaging Failed: ${env.BUILD_URL}"
        }
      }
    }
    stage('Build and Package on Ubuntu Jammy') {
      when {
        branch 'release'
        beforeAgent true
      }
      stages {
        stage('Build on Ubuntu Jammy') {
          agent {
            dockerfile {
              filename 'package/debian/Dockerfile'
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg BASE_IMAGE=ubuntu:jammy --build-arg LLVM_VERSION=14'
              reuseNode true
            }
          }
          stages {
            stage('Build Debian Package') {
              steps {
                dir("kframework-${env.VERSION}") {
                  checkout scm
                  sh '''
                    mv package/debian ./debian
                    mv debian/control.jammy debian/control
                    mv debian/compat.jammy debian/compat
                    mv debian/rules.jammy debian/rules
                    dpkg-buildpackage
                  '''
                }
                stash name: 'jammy', includes: "kframework_${env.VERSION}_amd64.deb"
              }
            }
          }
        }
        stage('Test Debian Package') {
          agent {
            docker {
              image 'ubuntu:jammy'
              args '-u 0'
              reuseNode true
            }
          }
          options { skipDefaultCheckout() }
          steps {
            unstash 'jammy'
            sh 'src/main/scripts/test-in-container-debian'
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
          slackSend color: '#cb2431'                                             \
                  , channel: '#k'                                                \
                  , message: "Ubuntu Jammy Packaging Failed: ${env.BUILD_URL}"
        }
      }
    }
    stage('Build and Package on Debian Bullseye') {
      when {
        branch 'release'
        beforeAgent true
      }
      stages {
        stage('Build on Debian Bullseye') {
          agent {
            dockerfile {
              filename 'package/debian/Dockerfile'
              additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg BASE_IMAGE=debian:bullseye --build-arg LLVM_VERSION=11'
              reuseNode true
            }
          }
          stages {
            stage('Build Debian Package') {
              steps {
                dir("kframework-${env.VERSION}") {
                  checkout scm
                  sh '''
                    mv package/debian ./debian
                    mv debian/control.debian debian/control
                    dpkg-buildpackage
                  '''
                }
                stash name: 'bullseye', includes: "kframework_${env.VERSION}_amd64.deb"
              }
            }
          }
        }
        stage('Test Debian Package') {
          agent {
            docker {
              image 'debian:bullseye'
              args '-u 0'
              reuseNode true
            }
          }
          options { skipDefaultCheckout() }
          steps {
            unstash 'bullseye'
            sh '''
              # echo "deb http://deb.debian.org/debian bullseye-backports main" > /etc/apt/sources.list.d/bullseye-backports.list
              src/main/scripts/test-in-container-debian
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
          slackSend color: '#cb2431'                                             \
                  , channel: '#k'                                                \
                  , message: "Debian Bullseye Packaging Failed: ${env.BUILD_URL}"
        }
      }
    }
    stage('Build and Package on Arch Linux') {
      when {
        branch 'release'
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
    stage('DockerHub') {
      when {
        branch 'release'
        beforeAgent true
      }
      environment {
        DOCKERHUB_TOKEN    = credentials('rvdockerhub')
        FOCAL_VERSION_TAG  = "ubuntu-focal-${env.VERSION}"
        FOCAL_BRANCH_TAG   = "ubuntu-focal-${env.BRANCH_NAME}"
        JAMMY_VERSION_TAG  = "ubuntu-jammy-${env.VERSION}"
        JAMMY_BRANCH_TAG   = "ubuntu-jammy-${env.BRANCH_NAME}"
        DOCKERHUB_REPO     = "runtimeverificationinc/kframework-k"
      }
      stages {
        stage('Build Image') {
          agent { label 'docker' }
          steps {
            milestone(2)
            dir('focal') { unstash 'focal' }
            sh '''
                mv focal/kframework_${VERSION}_amd64.deb kframework_amd64_focal.deb
                docker login --username "${DOCKERHUB_TOKEN_USR}" --password "${DOCKERHUB_TOKEN_PSW}"
                docker image build . --file package/docker/Dockerfile.ubuntu-focal --tag "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}"
                docker image push "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}"
                docker tag "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}" "${DOCKERHUB_REPO}:${FOCAL_BRANCH_TAG}"
                docker push "${DOCKERHUB_REPO}:${FOCAL_BRANCH_TAG}"
            '''
            dir('jammy') { unstash 'jammy' }
            sh '''
                mv jammy/kframework_${VERSION}_amd64.deb kframework_amd64_jammy.deb
                docker login --username "${DOCKERHUB_TOKEN_USR}" --password "${DOCKERHUB_TOKEN_PSW}"
                docker image build . --file package/docker/Dockerfile.ubuntu-jammy --tag "${DOCKERHUB_REPO}:${JAMMY_VERSION_TAG}"
                docker image push "${DOCKERHUB_REPO}:${JAMMY_VERSION_TAG}"
                docker tag "${DOCKERHUB_REPO}:${JAMMY_VERSION_TAG}" "${DOCKERHUB_REPO}:${JAMMY_BRANCH_TAG}"
                docker push "${DOCKERHUB_REPO}:${JAMMY_BRANCH_TAG}"
            '''
          }
        }
        stage('Test Focal Image') {
          agent {
            docker {
              image "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}"
              args '-u 0'
              reuseNode true
            }
          }
          steps {
            sh '''
              cd ~
              echo 'module TEST imports BOOL endmodule' > test.k
              kompile test.k --backend llvm
              kompile test.k --backend haskell
            '''
          }
        }
        stage('Test Jammy Image') {
          agent {
            docker {
              image "${DOCKERHUB_REPO}:${JAMMY_VERSION_TAG}"
              args '-u 0'
              reuseNode true
            }
          }
          steps {
            sh '''
              cd ~
              echo 'module TEST imports BOOL endmodule' > test.k
              kompile test.k --backend llvm
              kompile test.k --backend haskell
            '''
          }
        }
      }
    }
    stage('Deploy') {
      when {
        branch 'release'
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
        dir('focal')  { unstash 'focal' }
        dir('jammy')  { unstash 'jammy' }
        dir('bullseye') { unstash 'bullseye' }
        dir('arch')   { unstash 'arch'   }
        sshagent(['rv-jenkins-github']) {
          sh '''
            git clone 'ssh://github.com/runtimeverification/k.git' k-release
            cd k-release
            git fetch --all

            release_commit="$LONG_REV"
            git checkout $release_commit

            git tag -d "${K_RELEASE_TAG}"         || true
            git push -d origin "${K_RELEASE_TAG}" || true
            hub release delete "${K_RELEASE_TAG}" || true

            git tag "${K_RELEASE_TAG}" "${release_commit}"
            git push origin "${K_RELEASE_TAG}"

            mv ../kframework-${VERSION}-src.tar.gz                      kframework-${VERSION}-src.tar.gz
            mv ../focal/kframework_${VERSION}_amd64.deb                 kframework_${VERSION}_amd64_focal.deb
            mv ../jammy/kframework_${VERSION}_amd64.deb                 kframework_${VERSION}_amd64_jammy.deb
            mv ../bullseye/kframework_${VERSION}_amd64.deb              kframework_${VERSION}_amd64_bullseye.deb
            mv ../arch/kframework-git-${VERSION}-1-x86_64.pkg.tar.zst   kframework-git-${VERSION}-1-x86_64.pkg.tar.zst

            echo "K Framework Release ${VERSION}"  > release.md
            echo ''                               >> release.md
            cat k-distribution/INSTALL.md         >> release.md
            hub release create --prerelease                                                     \
                --attach kframework-${VERSION}-src.tar.gz'#Source tar.gz'                       \
                --attach kframework_${VERSION}_amd64_focal.deb'#Ubuntu Focal (20.04) Package'   \
                --attach kframework_${VERSION}_amd64_jammy.deb'#Ubuntu Jammy (22.04) Package'   \
                --attach kframework_${VERSION}_amd64_bullseye.deb'#Debian Bullseye (11) Package'    \
                --attach kframework-git-${VERSION}-1-x86_64.pkg.tar.zst'#Arch Package'          \
                --file release.md "${K_RELEASE_TAG}"
          '''
        }
      }
    }
    stage('GitHub Pages') {
      when {
        branch 'release'
        beforeAgent true
      }
      agent {
        dockerfile {
          additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
          reuseNode true
        }
      }
      post { failure { slackSend color: '#cb2431' , channel: '#k' , message: "GitHub Pages Deploy Failed: ${env.BUILD_URL}" } }
      steps {
        dir('gh-pages') {
          sshagent(['rv-jenkins-github']) {
            sh '''
              git clone 'ssh://github.com/runtimeverification/k.git' --depth 1 --no-single-branch --branch master --branch gh-pages
              cd k
              git checkout -B gh-pages origin/master
              git submodule update --init --recursive -- ./web
              cd web
              npm install
              npm run build
              npm run build-sitemap
              cd -
              mv web/public_content ./
              rm -rf $(find . -maxdepth 1 -not -name public_content -a -not -name .git -a -not -path . -a -not -path .. -a -not -name CNAME)
              mv public_content/* ./
              rm -rf public_content
              git add ./
              git commit -m 'gh-pages: Updated the website'
              git merge --strategy ours origin/gh-pages --allow-unrelated-histories
              git push origin gh-pages
            '''
          }
        }
      }
    }
    stage('Trigger Release') {
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
      options { skipDefaultCheckout() }
      post { failure { slackSend color: '#cb2431' , channel: '#k' , message: "Failed to trigger Release: ${env.BUILD_URL}" } }
      steps {
        sshagent(['rv-jenkins-github']) {
          sh '''
            git clone 'ssh://github.com/runtimeverification/k' k-release
            cd k-release
            git fetch --all
            git checkout -B release origin/release
            old_master="$(git merge-base origin/master origin/release)"
            new_master="$(git rev-parse origin/master)"
            if git diff --exit-code ${old_master} ${new_master} -- package/version; then
                git merge --no-edit origin/master
                ./package/version.sh bump
            else
                git merge --no-edit --strategy-option=theirs origin/master
            fi
            ./package/version.sh sub
            git add --update
            git commit --no-edit --allow-empty --message "Set Version: $(cat package/version)"
            git push origin release
          '''
        }
      }
    }
  }
}
