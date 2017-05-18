function runner(module, output){
  var state = module.emptyState;
  var init = module.init(state);
  var execute = module.execute(init.state, init.ids);
  for(var i = 0 ; i < execute.result.length ; i++){
    output(execute.result[i]);
  }
}
module.exports = runner;