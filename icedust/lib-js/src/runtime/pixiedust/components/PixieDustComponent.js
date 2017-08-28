var React = require('react');
var PropTypes = require('prop-types');
var Class = require('jsface').Class;

var PixieDustComponent = Class(React.Component, {
  constructor: function PixieDustComponent(props){
		
  },

  dispatch: function(action){
    this.context.store.dispatch(action);
  }
});

PixieDustComponent.contextTypes = {
  store: PropTypes.object
};

module.exports = PixieDustComponent;