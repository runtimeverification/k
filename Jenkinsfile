pipeline {
  agent {
    docker {
      image 'ubuntu:bionic'
    }

  }
  stages {
    stage('Build and Test') {
      steps {
        sh 'src/main/scripts/jenkins'
      }
    }
    stage('Deploy Nightly') {
      steps {
        sh 'src/main/scripts/nightly-release'
      }
    }
  }
}