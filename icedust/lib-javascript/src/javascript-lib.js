// lib
var vals = {};

vals.Output = function(el) {this.el = el};
vals.Output.prototype.get = function() {return this.el.innerHTML};
vals.Output.prototype.set = function(v) {this.el.innerHTML = v};
vals.Output.prototype.change = function(f) {};

vals.Input = function(el) {this.el = $(el)};
vals.Input.prototype.get = function() {return this.el.val()};
vals.Input.prototype.set = function(v) {this.el.val(v)};
vals.Input.prototype.change = function(f) {
	this.el.change(f);
	this.el.on('keyup', f);
};

vals.Checkbox = function(el) {this.el = el};
vals.Checkbox.prototype.get = function() {return this.el.checked};
vals.Checkbox.prototype.set = function(v) {this.el.checked = v};
vals.Checkbox.prototype.change = function(f) {
	this.el.addEventListener('change', f);
};

vals.Radios = function(el) {
	this.el = el;
	this.trueEl = el.querySelector('input[value="true"]');
	this.falseEl = el.querySelector('input[value="false"]');
	this.nullEl = el.querySelector('input[value="null"]');
};
vals.Radios.prototype.get = function() {
	if(this.trueEl.checked) return true;
	if(this.falseEl.checked) return false;
	if(this.nullEl.checked) return null;
};
vals.Radios.prototype.set = function(v) {
	if(v === true) {
		this.trueEl.checked = true;
		this.falseEl.checked = false;
		this.nullEl.checked = false;
	} else if(v === false) {
		this.trueEl.checked = false;
		this.falseEl.checked = true;
		this.nullEl.checked = false;
	} else if(v === null) {
		this.trueEl.checked = false;
		this.falseEl.checked = false;
		this.nullEl.checked = true;
	}
};
vals.Radios.prototype.change = function(f) {
	var radios = this.el.querySelectorAll('input[type="radio"]');
	for(var i = 0, l = radios.length; i < l; i++)
		radios[i].addEventListener('change', f);
};

var getVal = function(el) {
	var radios = el.querySelector('.optionalBoolean');
	if(radios) return new vals.Radios(radios);
	var checkbox = el.querySelector('input[type = "checkbox"]');
	if(checkbox) return new vals.Checkbox(checkbox);
	var inp = el.querySelector('input');
	if(inp instanceof HTMLInputElement)
		return new vals.Input(inp);
	var outp = el.querySelector('.output');
	if(outp) return new vals.Output(outp);
	throw new Error('Cannot recognize the element type for', el);
};

var elements = {};

var types = {};

types.Type = function() {};
types.Type.prototype.get = function() {return this.parse(this.val.get())};
types.Type.prototype.getRaw = function() {return this.val.get()};
types.Type.prototype.set = function(v) {return this.val.set(v)};
types.Type.prototype.setDerived = function(f) {this.derived = f};
types.Type.prototype.parse = function(v) {return v};
types.Type.prototype.check = function() {};
types.Type.prototype.flow = function() {
	if(!this.updates) return;
	for(var i = 0, a = this.updates, l = a.length; i < l; i++) {
		var update = a[i];
		if(elements[update])
			elements[update].refresh();
	}
};
types.Type.prototype.refresh = function() {
	if(this.derived) {
		if(this.isDefault) {
			var v = this.get();
			if(v === null || (typeof v === 'string' && v.trim().length === 0))
				this.setDefault(this.derived());
			else
				this.setDefault(v);
		} else {
			this.set(this.derived());
		}
	}
	var err = this.check();
	if(err) this.setError(err);
	else {
		this.setError('');
		this.flow();
	}
};
types.Type.prototype.setError = function(msg) {
	if(this.errEl) this.errEl.innerHTML = msg;
};
types.Type.prototype.setDefault = function(msg) {
	if(this.defaultEl) this.defaultEl.innerHTML = msg;
};
types.Type.prototype.init = function(el) {
	this.el = el;
	this.val = getVal(el);
	this.val.change(this.refresh.bind(this));
	this.name = el.getAttribute('data-name');

	var vUpdates = el.getAttribute('data-updates');
	this.updates = !vUpdates? []: vUpdates.split(/\s+/g);

	this.isDefault = el.getAttribute('data-default') === 'true';
	this.defaultEl = el.querySelector('.default-output');

	this.errEl = el.querySelector('.error-msg');

	this.derived = null;
};

var defType = function(name, check, parse) {
	types[name] = function(el) {this.init(el)};
	types[name].prototype = Object.create(types.Type.prototype);
	if(check) types[name].prototype.check = check;
	if(parse) types[name].prototype.parse = parse;
};

var partialVars = {};

var parsePartialVar = function(val, type) {
	if(type === 'String') return val || '';
	if(type === 'String?') return !val || val.trim('').length === 0? null: val;
	if(type === 'Int') return Math.floor(+val);
	if(type === 'Int?') return val === null || val === 'null'? null: Math.floor(+val);
	if(type === 'Float') return +val;
	if(type === 'Float?') return val === null || val === 'null'? null: +val;
	if(type === 'Boolean') return val === 'true';
	if(type === 'Boolean?') return val === null || val === 'null'? null: val === 'true';
};

window.addEventListener('load', function() {
	var els = document.querySelectorAll('[data-name]');
	for(var i = 0, l = els.length; i < l; i++) {
		var el = els[i];
		if(el.getAttribute('data-partial-var') === 'true') {
			partialVars[el.getAttribute('data-name')] =
				parsePartialVar(el.innerHTML, el.getAttribute('data-type'));
		} else {
			var type = el.getAttribute('data-type');
			var construct = types[type];
			if(!construct)
				console.error('Invalid type: ' + type);
			else
				elements[el.getAttribute('data-name')] = new construct(el);
		}
	}
	for(var k in elements) elements[k].refresh();
});

// Types
defType('String', function() {
	if(!this.isDefault && this.get().trim().length === 0)
		return this.name + ' cannot be empty!';
});
defType('String?');
defType('Int', function() {
	if(!this.isDefault && this.getRaw().trim().length === 0)
		return this.name + ' cannot be empty!';
	var v = this.get();
	if(isNaN(v)) return this.name + ' must be a number!';
	if(Math.floor(v) !== v) return this.name + ' must be an integer!';
}, function(v) {return +v});
defType('Int?', function() {
	if(this.getRaw().trim().length === 0) return null;
	var v = this.get();
	if(isNaN(v)) return this.name + ' must be a number!';
	if(Math.floor(v) !== v) return this.name + ' must be an integer!';
}, function(v) {return v.trim().length === 0? null: +v});
defType('Float', function() {
	if(!this.isDefault && this.getRaw().trim().length === 0)
		return this.name + ' cannot be empty!';
	if(isNaN(this.get())) return this.name + ' must be a number!';
}, function(v) {return +v});
defType('Float?', function() {
	if(this.getRaw().trim().length === 0) return null;
	if(isNaN(this.get())) return this.name + ' must be a number!';
}, function(v) {return v.trim().length === 0? null: +v});
defType('Boolean');
defType('Boolean?');

var parseDate = function(s) {
	if(s === null || s.trim().length === 0) return null;
	var t = s.match(/(\d+)\/(\d+)\/(\d+) (\d+):(\d+)/);
	return new Date(+t[3], (+t[2]) - 1, +t[1], +t[4], +t[5]);
};

defType('Datetime', function() {
	if(!this.isDefault && this.getRaw().trim().length === 0)
		return this.name + ' cannot be empty!';
}, parseDate);
defType('Datetime?', null, parseDate);

// api
var get = function(n) {return elements[n]? elements[n].get(): null};
var getPartialVar = function(n) {return typeof partialVars[n] !== 'undefined'? partialVars[n]: null};
var setDerived = function(n, f) {
	window.addEventListener('load', function() {
		if(elements[n]) elements[n].setDerived(f);
		for(var k in elements) elements[k].refresh();
	});
};

