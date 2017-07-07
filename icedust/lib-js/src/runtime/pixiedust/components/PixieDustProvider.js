var React = require('react');
var PropTypes = require('prop-types');
var Class = require('jsface').Class;

var PixieDustProvider = Class(React.Component, {
  constructor: function PixieDustProvider(props){

  },
  componentDidMount: function(){
    this.props.store.subscribe(this.forceUpdate.bind(this));
  },
  getChildContext: function(){
    return {
      store: this.props.store
    };
  },
  render: function(){
    return React.Children.only(this.props.children)
  }
});
PixieDustProvider.childContextTypes = {
    store: PropTypes.object
};

// class PixieDustProvider extends Component{
//   constructor(props){
//     super(props);
//   }
//
//   componentDidMount(){
//     this.props.store.subscribe(() => {
//       this.forceUpdate();
//     })
//   }
//
//   getChildContext(){
//     return {
//       store: this.props.store
//     }
//   }
//   render(){
//     return Children.only(this.props.children);
//   }
// }
// PixieDustProvider.childContextTypes = {
//   store: PropTypes.object
// };

module.exports = PixieDustProvider;