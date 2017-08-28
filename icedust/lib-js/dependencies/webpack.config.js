var path = require('path');
var webpack = require('webpack');

module.exports = {

  entry: {
    libraries: 'index'
  },
  output: {
    libraryTarget: 'commonjs2',
    path: path.join(__dirname, 'target'),
    filename: '[name].generated.js'
  },
  devtool: 'inline-source-map',
  resolve: {
    modules: [
      "node_modules",
      path.join(__dirname, 'src')
    ]
  },

  plugins: [
//    new webpack.optimize.UglifyJsPlugin({
//      compress: {
//        warnings: false,
//        drop_console: false
//      }
//    }),
//    new webpack.DefinePlugin({
//      'process.env.NODE_ENV': '"production"'
//    })
  ]
};