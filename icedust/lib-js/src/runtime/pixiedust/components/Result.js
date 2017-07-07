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

// class Result extends Component{
//   render(){
//     let result = this.props.result;
//     let entries = result.map((r, i) => <ResultEntry key={i} result={r}/>);
//     return <div>
//       { entries }
//     </div>;
//   }
// }

module.exports = Result;