node ('linux'){
  stage 'Build and Test'
  env.PATH = "${tool 'Maven 3'}/bin:${env.PATH}"
  checkout scm
  sh 'echo "QUALIFIER=$(date +%Y%m%d%H%M)" > build_env'
  sh 'mvn clean package'
}
