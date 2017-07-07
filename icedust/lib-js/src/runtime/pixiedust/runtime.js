var _ = require('lodash');
var redux = require('redux');
var React = require('react');
var ReactDOMServer = require('react-dom-server');

var PixieDustProvider = require('./components/PixieDustProvider');

var defaultDebug = false;
var defaultOptionalActions = ['@@redux/init', '@@INIT', '@@redux/INIT'];

var COMPOSE_ACTIONS = "composeActions";

var uniqueId = 0;
function generateUniqueId(){ //simple number generator
  return "" + uniqueId++;
}

function makeComposeActions(reducer){
  return function(state, message){
    for(var i = 0 ; i < message.actions.length ; i++){
      state = reducer(state, message.actions[i]);
    }
    return state;
  };
}

function composeActions(actions){
  return {
    type: COMPOSE_ACTIONS,
    actions: actions
  };
}


function makeReducer(actions, debug, optionalActions){
  if(debug === undefined){
    debug = defaultDebug;
  }

  actions = _.assign({}, actions); //clone actions

  if(optionalActions === undefined){
    optionalActions = defaultOptionalActions;
  }

  function reducer(state, message){
    var action = actions[message.type];
    if(action !== undefined){
      state = action(state, message)
    } else if(message.type !== undefined){
      if(optionalActions.indexOf(message.type) == -1){
        console.warn('unknown action: ' + message.type)
      }
    } else{
      console.warn('no message type is given')
    }
    if(state == undefined){
      throw new Error('state became empty after action ' + message.type);
    }
    return state;
  }

  actions[COMPOSE_ACTIONS] = makeComposeActions(reducer);

  if(debug) {
    return function(state, message){
      console.time(message.type);
      var result = reducer(state, message);
      console.timeEnd(message.type);
      return result;
    }
  }
  return reducer;
}


function makeStore(reducer, initialState){
  try{
    var devtools = window.__REDUX_DEVTOOLS_EXTENSION__ && window.__REDUX_DEVTOOLS_EXTENSION__();
    return redux.createStore(reducer, initialState, devtools);
  } catch(e){
    return redux.createStore(reducer, initialState);
  }
}

function castViewToString(store, view){
	var wrapped = React.createElement(PixieDustProvider, 
		{
			store: store
		}, 
		view
	);
	return ReactDOMServer.renderToStaticMarkup(wrapped);
}

module.exports = {
  generateUniqueId: generateUniqueId,
  makeReducer: makeReducer,
  makeStore: makeStore,
  castViewToString: castViewToString
};