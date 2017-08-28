var React = require('react');
var ReactDOMServer = require('react-dom-server');
var PixieDustProvider = require('./components/PixieDustProvider');

function renderToString(store, element){
  var wrappedElement = React.createElement(PixieDustProvider, {
    store: store
  }, element);
  return ReactDOMServer.renderToStaticMarkup(wrappedElement);
}

module.exports = {
  renderToString: renderToString
};