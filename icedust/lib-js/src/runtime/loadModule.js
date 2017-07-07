function loadModule(program){
  var scope = {
    exports: {}
  };
  program(require, scope);
  return scope.exports;
}
module.exports = loadModule;