var Class = require('jsface').Class;
var PixieDustComponent = require('./PixieDustComponent');
var Functions = require('lib/functions'); 


function Lifted(render){
	
	function constructor(props, context){
		this.materialize(props, context);
	}
	
	var LiftedComponent = Class(PixieDustComponent, {
		constructor: constructor,
		
    componentWillReceiveProps: function(props, context){
      this.materialize(props, context);
    },

    materialize: function(props, context){
      var state = context.store.getState();
      var rendered = render(props, state);
      this.materialized = rendered.result;
      if(rendered.state !== state){
        this.stateUpdate(context, rendered.state);
      }
    },

    stateUpdate: function(context, newState){
      context.store.dispatch({type: 'state_update', newState: newState})
    },

    render: function(){
      return this.materialized;
    }
  });
	Functions.tryRenameFunctionName(LiftedComponent, 'Lifted[' + render.name + ']');
  return LiftedComponent;
}

module.exports = Lifted;