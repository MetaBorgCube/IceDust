var React = require('react');
var Class = require('jsface').Class;
var _ = require('lodash');

var Lifted = require('./Lifted');


var ResultEntry = Class(React.Component, {
  constructor: function ResultEntry(props){
    
  },
  componentWillMount: function(){
    this.createLiftedValue();
  },

  createLiftedValue: function(){
    var result = this.props.result;
    function wrap(value){
      if(result.type !== 'View'){
        value = React.createElement('pre', {
          style: {
            whitespace: 'pre-wrap',
            wordWrap: 'break-word'
          }
        },
          value
        );
      }
      return value;
    }

    this.LiftedValue = Lifted(function(props, state){
      var calc = result.calculation(state);
      var value = calc.result;
      if(_.isArray(value)){
        value = React.createElement('div',
          value.map(function(e, i){ return React.createElement('div', {key: i}, wrap(e))})
        )
      } else{
        value = wrap(value);
      }
      return _.assign({}, calc, {result: value});
    })
  },

  render: function(){
    var result = this.props.result;
    var title = result.expression + " :: " + result.type + result.multiplicity;
    var LiftedValue = this.LiftedValue
    return React.createElement('div',
      {},
      React.createElement('h3',
        {},
        React.createElement('pre',
          {},
          title
        )
      ),
      React.createElement(LiftedValue)
    )
  }
});

// class ResultEntry extends Component{
//   componentWillMount(props){
//     this.bla();
//   }
//   componentWillReceiveProps(props){
//     if(this.props.result !== props.result){
//       this.bla()
//     }
//   }
//
//   bla(){
//     let result = this.props.result;
//     function wrap(value){
//       if(result.type !== 'View'){
//         value = <pre style={{whiteSpace: 'pre-wrap', wordWrap: 'break-word'}}> { value } </pre>
//       }
//       return value;
//     }
//
//     this.LiftedValue = Lifted(function(props, state){
//       let calc = result.calculation(state);
//       let value = calc.result;
//       if(_.isArray(value)){
//         value = <div>
//           { value.map((e, i) => <div key={i}>{wrap(e)}</div>) }
//         </div>;
//       } else{
//         value = wrap(value);
//       }
//       return _.assign({}, calc, {
//         result: value
//       });
//     });
//   }
//
//   render(){
//     let result = this.props.result;
//     let title = result.expression + " :: " + result.type + result.multiplicity;
//
//     let LiftedValue = this.LiftedValue;
//     return <div>
//       <h3><pre> { title } </pre></h3>
//       <LiftedValue/>
//     </div>;
//   }
// }

module.exports = ResultEntry;