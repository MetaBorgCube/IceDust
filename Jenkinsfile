node{
  stage('Build and Test'){
    try{
      notifyBuild('Started')
      checkout scm
      sh "git clean -fXd" // make sure generated files are removed (git-ignored files). Use "-fxd" to also remove untracked files, but note that this will also remove .repository forcing mvn to download all artifacts each build
      withMaven(
        mavenLocalRepo: '.repository',
        mavenSettingsConfig: 'org.jenkinsci.plugins.configfiles.maven.MavenSettingsConfig1430668968947',
        mavenOpts: '-Xmx1024m -Xss16m'
      ){
        // Run the maven build
        sh "mvn -B -U clean verify -DforceContextQualifier=\$(date +%Y%m%d%H%M) "
      }
      archiveArtifacts artifacts: 'icedust.eclipse.updatesite/target/site/', excludes: null, onlyIfSuccessful: true
      notifyBuild('Succeeded')
    } catch (e) {
      notifyBuild('Failed')
      throw e
    }
  }
}

def notifyBuild(String buildStatus) {
  // Message
  def message = """${buildStatus}: ${env.JOB_NAME} [${env.BUILD_NUMBER}] ${env.BUILD_URL}"""

  // Color
  if (buildStatus == 'Succeeded') {
    color = 'good'
  } else if (buildStatus == 'Failed') {
    color = 'danger'
  } else {
    color = '#4183C4' // Slack blue
  }

  // Send notifications
  slackSend (color: color, message: message, channel: '#webdsl2-dev')
}
