pipeline {
  agent { label 'docker' }
  options { ansiColor('xterm') }
  environment {
    PACKAGE         = 'kframework'
    ROOT_URL        = 'https://github.com/kframework/k/releases/download'
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
    stage('Build and Package K') {
      failFast true
      parallel {
        stage('Build and Package K on Linux') {
          stages {
            stage('Build and Package on Ubuntu Bionic') {
              when {
                anyOf {
                  branch 'release'
                  changeRequest()
                }
                beforeAgent true
              }
              stages {
                stage('Build on Ubuntu Bionic') {
                  agent {
                    dockerfile {
                      filename 'package/debian/Dockerfile'
                      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg BASE_IMAGE=ubuntu:bionic'
                      reuseNode true
                    }
                  }
                  stages {
                    stage('Checkout code') { steps { dir('k-exercises') { git url: 'git@github.com:kframework/k-exercises.git' } } }
                    stage('Build and Test K') {
                      options { timeout(time: 45, unit: 'MINUTES') }
                      steps {
                        sh '''
                          echo 'Setting up environment...'
                          eval `opam config env`
                          export K_OPTS='-Xmx12G'
                          echo 'Building K...'
                          mvn --batch-mode verify -U
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
                            mv debian/control.bionic debian/control
                            dpkg-buildpackage
                          '''
                        }
                        stash name: 'bionic', includes: "kframework_${env.VERSION}_amd64.deb"
                      }
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
                    unstash 'bionic'
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
            }
            stage('Build and Package on Ubuntu Focal') {
              when {
                branch 'release'
                beforeAgent true
              }
              stages {
                stage('Build on Ubuntu Focal') {
                  agent {
                    dockerfile {
                      filename 'package/debian/Dockerfile'
                      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg BASE_IMAGE=ubuntu:focal --build-arg LLVM_VERSION=10'
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
                            mv debian/control.focal debian/control
                            dpkg-buildpackage
                          '''
                        }
                        stash name: 'focal', includes: "kframework_${env.VERSION}_amd64.deb"
                      }
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
            stage('Build and Package on Debian Buster') {
              when {
                branch 'release'
                beforeAgent true
              }
              stages {
                stage('Build on Debian Buster') {
                  agent {
                    dockerfile {
                      filename 'package/debian/Dockerfile'
                      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g) --build-arg BASE_IMAGE=debian:buster --build-arg LLVM_VERSION=8'
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
                        stash name: 'buster', includes: "kframework_${env.VERSION}_amd64.deb"
                      }
                    }
                  }
                }
                stage('Test Debian Package') {
                  agent {
                    docker {
                      image 'debian:buster'
                      args '-u 0'
                      reuseNode true
                    }
                  }
                  options { skipDefaultCheckout() }
                  steps {
                    unstash 'buster'
                    sh '''
                      echo "deb http://deb.debian.org/debian buster-backports main" > /etc/apt/sources.list.d/buster-backports.list
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
                          , message: "Debian Buster Packaging Failed: ${env.BUILD_URL}"
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
                      pacman -S --noconfirm opam pkgconf
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
          }
        }
        stage('Build and Package on Mac OS') {
          when {
            branch 'release'
            beforeAgent true
          }
          options { timeout(time: 150, unit: 'MINUTES') }
          stages {
            stage('Build on Mac OS') {
              stages {
                stage('Build Homebrew Bottle') {
                  agent { label 'anka' }
                  environment { STACK_ROOT = '/opt/stack' }
                  steps {
                    unstash 'src'
                    dir('kframework') { checkout scm }
                    dir('homebrew-k') {
                      git url: 'git@github.com:kframework/homebrew-k.git'
                      sh '''
                        git config --global user.email 'admin@runtimeverification.com'
                        git config --global user.name  'RV Jenkins'
                        # Note: double-backslash in sed-command is for Jenkins benefit.
                        brew_base_branch=$(cd ../kframework && git log -n1 --format=%s HEAD | sed -n 's!.*\\[brew-staging: \\(.*\\)\\].*!\\1!p')
                        [ "$brew_base_branch" != '' ] || brew_base_branch=master
                        git show-ref --verify refs/remotes/origin/$brew_base_branch
                        git push -d origin brew-release-$PACKAGE || true
                        git checkout -b brew-release-$PACKAGE "origin/$brew_base_branch"
                        git merge origin/master
                        ${WORKSPACE}/package/macos/brew-update-to-local ${PACKAGE} ${VERSION}
                        git commit Formula/$PACKAGE.rb -m "Update ${PACKAGE} to ${SHORT_REV}: part 1"
                        ${WORKSPACE}/package/macos/brew-build-and-update-to-local-bottle ${PACKAGE} ${VERSION} ${ROOT_URL}
                        git commit Formula/$PACKAGE.rb -m "Update ${PACKAGE} to ${SHORT_REV}: part 2"
                        git push origin brew-release-$PACKAGE
                      '''
                      stash name: 'big_sur', includes: "kframework--${env.VERSION}.big_sur.bottle*.tar.gz"
                    }
                  }
                }
                stage('Test Homebrew Bottle') {
                  agent { label 'anka' }
                  steps {
                    dir('homebrew-k') {
                      git url: 'git@github.com:kframework/homebrew-k.git', branch: 'brew-release-kframework'
                      unstash 'big_sur'
                      sh '${WORKSPACE}/package/macos/brew-install-bottle ${PACKAGE} ${VERSION}'
                    }
                    sh '''
                      brew install opam pkg-config
                      k-configure-opam
                      eval $(opam config env)
                      cp -R /usr/local/share/kframework/pl-tutorial ~
                      WD=`pwd`
                      cd
                      echo 'Starting kserver...'
                      spawn-kserver $WD/kserver.log
                      cd pl-tutorial
                      echo 'Testing tutorial in user environment...'
                      make -j`sysctl -n hw.ncpu` ${MAKE_EXTRA_ARGS}
                      cd ~
                      echo 'module TEST imports BOOL endmodule' > test.k
                      kompile test.k --backend ocaml
                      kompile test.k --backend llvm
                      kompile test.k --backend haskell
                    '''
                    dir('homebrew-k') {
                      sh '''
                        ${WORKSPACE}/package/macos/brew-update-to-final ${PACKAGE} ${VERSION} ${ROOT_URL}
                        git commit Formula/$PACKAGE.rb -m "Update ${PACKAGE} to ${SHORT_REV}: part 3"
                        git push origin brew-release-$PACKAGE
                      '''
                    }
                  }
                  post {
                    always {
                      sh 'stop-kserver || true'
                      archiveArtifacts 'kserver.log,k-distribution/target/kserver.log'
                    }
                  }
                }
              }
              post { always { archiveArtifacts artifacts: 'kserver.log,k-distribution/target/kserver.log', allowEmptyArchive: true } }
            }
          }
          post {
            failure {
              slackSend color: '#cb2431'                                    \
                      , channel: '#k'                                       \
                      , message: "MacOS Packaging Failed: ${env.BUILD_URL}"
            }
          }
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
        BIONIC_VERSION_TAG = "ubuntu-bionic-${env.VERSION}"
        BIONIC_BRANCH_TAG  = "ubuntu-bionic-${env.BRANCH_NAME}"
        FOCAL_VERSION_TAG  = "ubuntu-focal-${env.VERSION}"
        FOCAL_BRANCH_TAG   = "ubuntu-focal-${env.BRANCH_NAME}"
        DOCKERHUB_REPO     = "runtimeverificationinc/kframework-k"
      }
      stages {
        stage('Build Image') {
          agent { label 'docker' }
          steps {
            milestone(2)
            dir('bionic') { unstash 'bionic' }
            sh '''
                mv bionic/kframework_${VERSION}_amd64.deb kframework_amd64_bionic.deb
                docker login --username "${DOCKERHUB_TOKEN_USR}" --password "${DOCKERHUB_TOKEN_PSW}"
                docker image build . --file package/docker/Dockerfile.ubuntu-bionic --tag "${DOCKERHUB_REPO}:${BIONIC_VERSION_TAG}"
                docker image push "${DOCKERHUB_REPO}:${BIONIC_VERSION_TAG}"
                docker tag "${DOCKERHUB_REPO}:${BIONIC_VERSION_TAG}" "${DOCKERHUB_REPO}:${BIONIC_BRANCH_TAG}"
                docker push "${DOCKERHUB_REPO}:${BIONIC_BRANCH_TAG}"
            '''
            dir('focal') { unstash 'focal' }
            sh '''
                mv focal/kframework_${VERSION}_amd64.deb kframework_amd64_focal.deb
                docker login --username "${DOCKERHUB_TOKEN_USR}" --password "${DOCKERHUB_TOKEN_PSW}"
                docker image build . --file package/docker/Dockerfile.ubuntu-focal --tag "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}"
                docker image push "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}"
                docker tag "${DOCKERHUB_REPO}:${FOCAL_VERSION_TAG}" "${DOCKERHUB_REPO}:${FOCAL_BRANCH_TAG}"
                docker push "${DOCKERHUB_REPO}:${FOCAL_BRANCH_TAG}"
            '''
          }
        }
        stage('Test Bionic Image') {
          agent {
            docker {
              image "${DOCKERHUB_REPO}:${BIONIC_VERSION_TAG}"
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
        dir('bionic') { unstash 'bionic' }
        dir('focal')  { unstash 'focal' }
        dir('buster') { unstash 'buster' }
        dir('arch')   { unstash 'arch'   }
        dir('big_sur') { unstash 'big_sur' }
        sshagent(['rv-jenkins-github']) {
          sh '''
            git clone 'ssh://github.com/kframework/k.git' k-release
            cd k-release
            git fetch --all

            release_commit="$(git merge-base $LONG_REV origin/master)"
            git checkout $release_commit

            git tag -d "${K_RELEASE_TAG}"         || true
            git push -d origin "${K_RELEASE_TAG}" || true
            hub release delete "${K_RELEASE_TAG}" || true

            git tag "${K_RELEASE_TAG}" "${release_commit}"
            git push origin "${K_RELEASE_TAG}"

            LOCAL_BOTTLE_NAME=$(find ../big_sur -name "kframework--${VERSION}.big_sur.bottle*.tar.gz")
            BOTTLE_NAME=$(echo ${LOCAL_BOTTLE_NAME#../big_sur/} | sed 's!kframework--!kframework-!')

            mv ../kframework-${VERSION}-src.tar.gz                      kframework-${VERSION}-src.tar.gz
            mv ../bionic/kframework_${VERSION}_amd64.deb                kframework_${VERSION}_amd64_bionic.deb
            mv ../focal/kframework_${VERSION}_amd64.deb                 kframework_${VERSION}_amd64_focal.deb
            mv ../buster/kframework_${VERSION}_amd64.deb                kframework_${VERSION}_amd64_buster.deb
            mv ../arch/kframework-git-${VERSION}-1-x86_64.pkg.tar.zst   kframework-git-${VERSION}-1-x86_64.pkg.tar.zst
            mv $LOCAL_BOTTLE_NAME                                       $BOTTLE_NAME

            echo "K Framework Release ${VERSION}"  > release.md
            echo ''                               >> release.md
            cat k-distribution/INSTALL.md         >> release.md
            hub release create                                                                  \
                --attach kframework-${VERSION}-src.tar.gz'#Source tar.gz'                       \
                --attach kframework_${VERSION}_amd64_bionic.deb'#Ubuntu Bionic (18.04) Package' \
                --attach kframework_${VERSION}_amd64_focal.deb'#Ubuntu Focal (20.04) Package'   \
                --attach kframework_${VERSION}_amd64_buster.deb'#Debian Buster (10) Package'    \
                --attach kframework-git-${VERSION}-1-x86_64.pkg.tar.zst'#Arch Package'          \
                --attach $BOTTLE_NAME'#Mac OS X Homebrew Bottle'                                \
                --file release.md "${K_RELEASE_TAG}"
          '''
        }
        dir('homebrew-k') {
          git url: 'git@github.com:kframework/homebrew-k.git', branch: 'brew-release-kframework'
          sshagent(['rv-jenkins-github']) {
            sh '''
              git checkout master
              git merge brew-release-$PACKAGE
              git push origin master
              git push origin -d brew-release-$PACKAGE
            '''
          }
        }
      }
    }
    stage('Update Dependents') {
      when {
        branch 'release'
        beforeAgent true
      }
      steps {
        build job: 'DevOps/master', propagate: false, wait: false                                       \
            , parameters: [ booleanParam ( name: 'UPDATE_DEPS'         , value: true                  ) \
                          , string       ( name: 'UPDATE_DEPS_REPO'    , value: 'kframework/k'        ) \
                          , string       ( name: 'UPDATE_DEPS_VERSION' , value: "${env.K_RELEASE_TAG}") \
                          ]
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
              git clone 'ssh://github.com/kframework/k.git' --depth 1 --no-single-branch --branch master --branch gh-pages
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
            git clone 'ssh://github.com/kframework/k' k-release
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
