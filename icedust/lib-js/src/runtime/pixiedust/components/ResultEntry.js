var React = require('react');
var Class = require('jsface').Class;
var _ = require('lodash');
var Functions = require('lib/functions');

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
            whiteSpace: 'pre-wrap',
            wordWrap: 'break-word'
          }
        },
          value
        );
      }
      return value;
    }

    
    function lift(props, state){
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
    }
    
    Functions.tryRenameFunctionName(lift, result.expression);
    
    this.LiftedValue = Lifted(lift)
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

module.exports = ResultEntry;