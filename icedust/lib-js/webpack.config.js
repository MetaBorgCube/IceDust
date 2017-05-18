var path = require('path');
var fs = require('fs');
var webpack = require('webpack');

module.exports = {
  entry: ['./runner'],

  output: {
    path: 'target/',
    publicPath: 'http://localhost:3001/',
    filename: '[name].js',
    chunkFilename: '[chunkhash].js'
  },

  module: {
    loaders: [
      {
        test: /\.js$/,
        exclude: /node_modules/,
        loader: 'babel',
        query: {
          presets: ['es2015'],
        }
      }
    ]
  },

  resolve: {
    modulesDirectories: [
      'node_modules',
      __dirname
    ]
  },
  devtool: 'eval',

  plugins: [
    new webpack.optimize.UglifyJsPlugin()
  ]
};
