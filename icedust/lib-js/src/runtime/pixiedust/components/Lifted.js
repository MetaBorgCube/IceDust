var Class = require('jsface').Class;
var PixieDustComponent = require('./PixieDustComponent');

function Lifted(render){
  var LiftedComponent = Class(PixieDustComponent, {
    constructor: function LiftedComponent(props, context){
      this.materialize(props, context);
    },

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
      console.log(this.materialized);
      return this.materialized;
    }
  });
  return LiftedComponent;
}

// function Lifted(render){
//
//   class LiftedComponent extends PixieDustComponent {
//     constructor(props, context) {
//       super(props);
//       this.materalize(props, context);
//     }
//
//     componentWillMount(props){
//       // this.materalize(props, this.context)
//     }
//
//     componentWillReceiveProps(props, context) {
//       this.materalize(props, context);
//     }
//
//     materalize(props, context){
//       let state = context.store.getState();
//       let rendered = render(props, state);
//       this.materialized = rendered.result;
//       if(rendered.state !== state){
//         this.stateUpdate(context, rendered.state);
//       }
//     }
//
//     stateUpdate(context, newState){
//       context.store.dispatch({type: 'state_update', newState: newState})
//     }
//
//     render() {
//       return this.materialized;
//     }
//   }
//   return LiftedComponent;
// }
module.exports = Lifted;