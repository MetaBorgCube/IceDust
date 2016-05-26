// lib
var getterInput = function(id) {
	return function() {
		return document.getElementById(id).children[0].value;
	};
};
var setterInput = function(id) {
	return function(val) {
		document.getElementById(id).children[0].value = val;
	};
};
var getterOutput = function(id) {
	return function() {
		return document.getElementById(id).innerHTML;
	};
};
var setterOutput = function(id) {
	return function(val) {
		document.getElementById(id).innerHTML = val;
	};
};
var id = function(x) {return x};
var input = function(id) {
	return {
		get: getterInput(id),
		set: setterInput(id),
		refresh: id
	};
};
var derived = function(id, fn) {
	var set = setterOutput(id);
	return {
		get: getterOutput(id),
		set: set,
		refresh: function() { set(fn()) }
	};
};

var attrs = {};

var get = function(id) {return attrs[id].get()};

var addInput = function(id) {
	attrs[id] = input(id);
};
var addDerived = function(id, f) {
	attrs[id] = derived(id, f);
};

window.onload = function() {
	var inputs = document.querySelectorAll('.input');
	for(var i = 0, l = inputs.length; i < l; i++) {
		var inpWrapper = inputs[i];
		var flowsTo = inpWrapper.getAttribute("data-flows-to").split(/\s+/g);
		var inp = inpWrapper.children[0];
		inp.onchange = inp.onkeyup = function() {
			for(var i = 0, l = flowsTo.length; i < l; i++)
				attrs[flowsTo[i]].refresh();
		};
	}
};

// generated

addInput('personName');
addDerived('derived', function() {
	return "You are " + get('personName');
});
