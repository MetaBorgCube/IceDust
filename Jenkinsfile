def getWorkspace() {
    pwd().replace("%2F", "_")
}

node{
  ws(getWorkspace()) {
    stage 'Build and Test'
    checkout scm
    sh 'echo "QUALIFIER=$(date +%Y%m%d%H%M)" > build_env'
    withMaven(
      mavenLocalRepo: '.repository',
      mavenSettingsConfig: 'org.jenkinsci.plugins.configfiles.maven.MavenSettingsConfig1430668968947',
      mavenOpts: '-Xmx1024m -Xss16m'
    ){
      // Run the maven build
      sh "mvn clean verify -B"
    }
    archiveArtifacts artifacts: 'icedust.eclipse.updatesite/target/site/', excludes: null, onlyIfSuccessful: true
  }
}
