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

            echo "K Framework Release ${VERSION}"  > release.md
            echo ''                               >> release.md
            cat k-distribution/INSTALL.md         >> release.md
            hub release create --prerelease                                                      \
                --file release.md "${K_RELEASE_TAG}"
          '''
        }
      }
    }
  }
}
