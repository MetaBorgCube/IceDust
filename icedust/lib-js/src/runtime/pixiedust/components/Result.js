var React = require('react');
var Class = require('jsface').Class;

var ResultEntry = require('./ResultEntry')


var Result = Class(React.Component, {
  constructor: function Result(props){

  },
  render: function(){
    var result = this.props.result;
    var entries = result.map(function(r, i){
      return React.createElement(ResultEntry, {
        key: i,
        result: r
      });
    });
    return React.createElement('div', {}, entries);
  }
});

module.exports = Result;