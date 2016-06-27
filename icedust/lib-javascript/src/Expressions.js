
/**
 * Expression.js
 *
 * @author: Albert ten Napel
 * @date: 2016-04-28
 *
 * This is a translation of Expressions.java from the IceDust project to JavaScript.
 *
 * Translations:
 * 	Collection -> Array
 * 	Float/Integer/float/int -> Number
 * 	Boolean/boolean -> Boolean
 * 	String -> String
 *	Date -> Date
 *	null -> null
 *
 */

// helper methods

function toCollection(e) {
	return e === null ? [] : [e];
}

function equals(a, b) {
	if(a === null) return b === null;
	if(Array.isArray(a)) {
		if(!Array.isArray(b)) return false;
		if(a.length !== b.length) return false;
		for(var i = 0, l = a.length; i < l; i++) {
			if(!equals(a[i], b[i])) return false;
		}
		return true;
	}
	return a === b;
}

/**
 * add all elements in array b to array a
 */
function addAll(a, b) {
	for(var i = 0, l = b.length; i < l; i++) {
		a.push(b[i]);
	}
	return a;
}

// multiplicity expressions

function choice_One_One(e1, e2) {
	return e1 !== null ? e1 : e2;
}

function choice_One_Many(e1, e2) {
	return e1 !== null ? toCollection(e1) : e2;
}

function choice_Many_One(e1, e2) {
	return e1.length > 0 ? e1 : e2 !== null ? toCollection(e2) : e1;
}

function choice_Many_Many(e1, e2) {
	return e1.length > 0 ? e1 : e2;
}

function merge_One_One(e1, e2) {
	var c = [];
	if (e1 !== null)
		c.push(e1);
	if (e2 !== null)
		c.push(e2);
	return c;
}

function merge_One_Many(e1, e2) {
	var c = [];
	if (e1 !== null)
		c.push(e1);
	addAll(c, e2);
	return c;
}

function merge_Many_One(e1, e2) {
	var c = [];
	addAll(c, e1);
	if (e2 !== null)
		c.push(e2);
	return c;
}

function merge_Many_Many(e1, e2) {
	var c = [];
	addAll(c, e1);
	addAll(c, e2);
	return c;
}

// math expressions

function plus_NullType(i, j) {
	return null;
}

function plus_String(i, j) {
	return i !== null && j !== null ? i + j : null;
}

function plus_Number(i, j) {
	return i !== null && j !== null ? i + j : null;
}
var plus_Float = plus_Integer = plus_Number;

function minus_NullType(i, j) {
	return null;
}

function minus_Number(i, j) {
	return i !== null && j !== null ? i - j : null;
}
var minus_Float = minus_Integer = minus_Number;

function minus_Date(i, j) {
	return i !== null && j !== null ?
		(i.getTime() - j.getTime()) / 1000:
		null;
}

function mul_NullType(i, j) {
	return null;
}

function mul_Number(i, j) {
	return i !== null && j !== null ? i * j : null;
}
var mul_Float = mul_Integer = mul_Number;

function mod_NullType(i, j) {
	return null;
}

function mod_Number(i, j) {
	return i !== null && j !== null && j !== 0 ? i % j : null;
}
var mod_Float = mod_Integer = mod_Number;

function div_NullType(i, j) {
	return null;
}

function div_Number(i, j) {
	return i !== null && j !== null && j !== 0 ? i / j : null;
}
var div_Float = div_Integer = div_Number;

function floordiv_NullType(i, j) {
	return null;
}

function floordiv_Number(i, j) {
	return i !== null && j !== null && j !== 0 ? Math.floor(i / j) : null;
}
var floordiv_Float = floordiv_Integer = floordiv_Number;

// aggregation expressions

function avg_NullType(i, j) {
	return null;
}

function avg_Number(c) {
	var l = c.length;
	if (l === 0)
		return null;
	var sum = 0;
	for(var i = 0; i < l; i++) {
		sum += c[i];
	}
	return sum / l;
}
var avg_Float = avg_Integer = avg_Number;

function sum_NullType(i, j) {
	return null;
}

function sum_Number(c) {
	var sum = 0;
	for(var i = 0, l = c.length; i < l; i++) {
		sum += c[i];
	}
	return sum;
}
var sum_Float = sum_Integer = sum_Number;

function max_NullType(i, j) {
	return null;
}

function max_Number(c) {
	if (c.length === 0)
		return null;
	var max = Number.MIN_VALUE;
	for(var i = 0, l = c.length; i < l; i++) {
		var cur = c[i];
		if(cur > max) {
			max = cur;
		}
	}
	return max;
}
var max_Float = max_Integer = max_Number;

function min_NullType(i, j) {
	return null;
}

function min_Number(c) {
	if (c.length === 0)
		return null;
	var min = Number.MAX_VALUE;
	for(var i = 0, l = c.length; i < l; i++) {
		var cur = c[i];
		if(cur < min) {
			min = cur;
		}
	}
	return min;
}
var min_Float = min_Integer = min_Number;

function conj(b) {
	var conj = true;
	for(var i = 0, l = b.length; i < l; i++) {
		conj = conj && b[i];
	}
	return conj;
}

function disj(b) {
	var disj = false;
	for(var i = 0, l = b.length; i < l; i++) {
		disj = disj || b[i];
	}
	return disj;
}

function concat(c) {
	if (c.length === 0)
		return null;
	return c.join('');
}

function count(c) {
	return Array.isArray(c) ? c.length : c === null ? 0 : 1;
}

// logic expressions

function not_Boolean(e) {
	return e === null ? null : !e;
}

function lt_NullType(i, j) {
	return null;
}

function lt_Number(i, j) {
	return i !== null && j !== null ? i < j : null;
}
var lt_Float = lt_Integer = lt_Number;

function lt_Date(i, j) {
	return i !== null && j !== null ? i.getTime() < j.getTime() : null;
}

function lte_NullType(i, j) {
	return null;
}

function lte_Number(i, j) {
	return i !== null && j !== null ? i <= j : null;
}
var lte_Float = lte_Integer = lte_Number;

function lte_Date(i, j) {
	return i !== null && j !== null ? i.getTime() <= j.getTime() : null;
}

function gt_NullType(i, j) {
	return null;
}

function gt_Number(i, j) {
	return i !== null && j !== null ? i > j : null;
}
var gt_Float = gt_Integer = gt_Number;

function gt_Date(i, j) {
	return i !== null && j !== null ? i.getTime() > j.getTime() : null;
}

function gte_NullType(i, j) {
	return null;
}

function gte_Number(i, j) {
	return i !== null && j !== null ? i >= j : null;
}
var gte_Float = gte_Integer = gte_Number;

function gte_Date(i, j) {
	return i !== null && j !== null ? i.getTime() >= j.getTime() : null;
}

function and(i, j) {
	return i !== null && j !== null ? i && j : null;
}

function or(i, j) {
	return i !== null && j !== null ? i || j : null;
}

// logic expressions : equality

function eq_One_One(i, j) {
	return i === null || j === null ? null : i === j;
}

function eq_One_Many(i, j) {
	return i === null || j.length === 0 ? null : equals(toCollection(i), j);
}

function eq_Many_One(i, j) {
	return i.length === 0 || j === null ? null : equals(toCollection(j), i);
}

function eq_Many_Many(i, j) {
	return i.length === 0 || j.length === 0 ? null : equals(i, j);
}

function neq_One_One(i, j) {
	return i === null || j === null ? null : i !== j;
}

function neq_One_Many(i, j) {
	return i === null || j.length === 0 ? null : !equals(toCollection(i), j);
}

function neq_Many_One(i, j) {
	return i.length === 0 || j === null ? null : !equals(toCollection(j), i);
}

function neq_Many_Many(i, j) {
	return i.length === 0 || j.length === 0 ? null : !equals(i, j);
}

// logic expressions : conditional

function conditional_One_One_One(b, i, j) {
	return b === null ? null : b ? i : j;
}

function conditional_One_One_Many(b, i, j) {
	return b === null ? [] : b ? toCollection(i) : j;
}

function conditional_One_Many_One(b, i, j) {
	return b === null ? [] : b ? i : toCollection(j);
}

function conditional_One_Many_Many(b, i, j) {
	return b === null ? [] : b ? i : j;
}

// cast expressions

function asFloat(is) {
	if(!Array.isArray(is))
		return is === null ? null : +is;
	var c = [];
	for(var i = 0, l = is.length; i < l; i++) {
		c.push(is[i]);
	}
	return c;
}

function asInteger(is) {
	if(!Array.isArray(is))
		return is === null ? null : Math.floor(+is);
	var c = [];
	for(var i = 0, l = is.length; i < l; i++) {
		c.push(Math.floor(is[i]));
	}
	return c;
}

function asString(is) {
	if(!Array.isArray(is))
		return is === null ? null : '' + is;
	var c = [];
	for(var i = 0, l = is.length; i < l; i++) {
		c.push('' + is[i]);
	}
	return c;
}

// literals
function parseDatetime(s) {
	if(s === null || s.trim().length === 0) return null;
	var t = s.match(/^(\d+)\/(\d+)\/(\d+) (\d+):(\d+)$/);
	if(t)
		return new Date(+t[3], (+t[2]) - 1, +t[1], +t[4], +t[5]);
	t = s.match(/^(\d+)\/(\d+)\/(\d+) (\d+):(\d+):(\d+)\.(\d+)$/);
	if(t)
		return new Date(+t[3], (+t[2]) - 1, +t[1], +t[4], +t[5], +t[6], +t[7]);
	return null;
}
