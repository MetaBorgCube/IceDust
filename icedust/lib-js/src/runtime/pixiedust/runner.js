var loadModule = require('../loadModule');
var React = require('react');
var ReactDOM = require('react-dom');

var Result = require('./components/Result');
var PixieDustProvider = require('./components/PixieDustProvider');
var PixieDustComponent = require('./components/PixieDustComponent');

var runtime = require('./runtime');

function runner(program, container){
  var module = loadModule(program);
  var state = module.emptyState;
  var init = module.init(state);
  var store = runtime.makeStore(module.reducer, init.state);
  var execute = module.execute(store, init.ids);

  var element = React.createElement(
    PixieDustProvider,
    {
      store: store
    },
      React.createElement(
        Result,
        {
          result: execute
        }
      )
    );
  ReactDOM.render(element, container);
  console.log('result', execute);
  console.log('state', store.getState().toJS());

}

module.exports = runner;