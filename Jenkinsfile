// workaround for branch-names which contain a slash
def getWorkspace() {
    pwd().replace("%2F", "_")
}

node{
  ws(getWorkspace()) {
    stage 'Build and Test'
    checkout scm
    withMaven(
      mavenLocalRepo: '.repository',
      mavenSettingsConfig: 'org.jenkinsci.plugins.configfiles.maven.MavenSettingsConfig1430668968947',
      mavenOpts: '-Xmx1024m -Xss16m'
    ){
      // Run the maven build
      sh "mvn -B -U clean verify -DforceContextQualifier=\$(date +%Y%m%d%H%M) "
    }
    archiveArtifacts artifacts: 'icedust.eclipse.updatesite/target/site/', excludes: null, onlyIfSuccessful: true
  }
}
