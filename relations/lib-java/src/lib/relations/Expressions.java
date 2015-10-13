package lib.relations;

import java.util.ArrayList;
import java.util.Collection;

public class Expressions {

	// helper methods

	public static <E> Collection<E> emptyCollection() {
		return new ArrayList<E>();
	}

	public static <E> Collection<E> toCollection(E e) {
		Collection<E> collection = emptyCollection();
		if (e != null)
			collection.add(e);
		return collection;
	}

	// multiplicity expressions

	public static <E> E choice(E e1, E e2) {
		return e1 != null ? e1 : e2;
	}

	public static <E> Collection<E> choice(E e1, Collection<E> e2) {
		return e1 != null ? toCollection(e1) : e2;
	}

	public static <E> Collection<E> choice(Collection<E> e1, E e2) {
		return e1.size() > 0 ? e1 : e2 != null ? toCollection(e2) : e1;
	}

	public static <E> Collection<E> choice(Collection<E> e1, Collection<E> e2) {
		return e1.size() > 0 ? e1 : e2;
	}

	public static <E> Collection<E> merge(E e1, E e2) {
		Collection<E> c = emptyCollection();
		if (e1 != null)
			c.add(e1);
		if (e2 != null)
			c.add(e2);
		return c;
	}

	public static <E> Collection<E> merge(E e1, Collection<E> e2) {
		Collection<E> c = emptyCollection();
		if (e1 != null)
			c.add(e1);
		c.addAll(e2);
		return c;
	}

	public static <E> Collection<E> merge(Collection<E> e1, E e2) {
		Collection<E> c = emptyCollection();
		c.addAll(e1);
		if (e2 != null)
			c.add(e2);
		return c;
	}

	public static <E> Collection<E> merge(Collection<E> e1, Collection<E> e2) {
		Collection<E> c = emptyCollection();
		c.addAll(e1);
		c.addAll(e2);
		return c;
	}

	// math expressions

	public static String plus(String i, String j) {
		return i != null && j != null ? i + j : null;
	}

	public static Integer plus(Integer i, Integer j) {
		return i != null && j != null ? i + j : null;
	}

	public static Float plus(Float i, Float j) {
		return i != null && j != null ? i + j : null;
	}

	public static Integer minus(Integer i, Integer j) {
		return i != null && j != null ? i - j : null;
	}

	public static Float minus(Float i, Float j) {
		return i != null && j != null ? i - j : null;
	}

	public static Integer mul(Integer i, Integer j) {
		return i != null && j != null ? i * j : null;
	}

	public static Float mul(Float i, Float j) {
		return i != null && j != null ? i * j : null;
	}

	public static Integer mod(Integer i, Integer j) {
		return i != null && j != null && j != 0 ? i % j : null;
	}

	public static Float mod(Float i, Float j) {
		return i != null && j != null && j != 0 ? i % j : null;
	}

	public static Integer div(Integer i, Integer j) {
		return i != null && j != null && j != 0 ? i / j : null;
	}

	public static Float div(Float i, Float j) {
		return i != null && j != null && j != 0 ? i / j : null;
	}

	// aggregation expressions

	public static Integer avg_Integer(Collection<Integer> c) {
		if (c.size() == 0)
			return null;
		int sum = 0;
		for (int i : c) {
			sum += i;
		}
		return sum / c.size();
	}

	public static Float avg_Float(Collection<Float> c) {
		if (c.size() == 0)
			return null;
		float sum = 0;
		for (float i : c) {
			sum += i;
		}
		return sum / c.size();
	}

	public static Integer sum_Integer(Collection<Integer> c) {
		int sum = 0;
		for (int i : c) {
			sum += i;
		}
		return sum;
	}

	public static Float sum_Float(Collection<Float> c) {
		float sum = 0;
		for (float i : c) {
			sum += i;
		}
		return sum;
	}

	public static Integer max_Integer(Collection<Integer> c) {
		if (c.size() == 0)
			return null;
		int max = Integer.MIN_VALUE;
		for (int i : c) {
			max = Math.max(max, i);
		}
		return max;
	}

	public static Float max_Float(Collection<Float> c) {
		if (c.size() == 0)
			return null;
		float max = Float.MIN_VALUE;
		for (float i : c) {
			max = Math.max(max, i);
		}
		return max;
	}

	public static Integer min_Integer(Collection<Integer> c) {
		if (c.size() == 0)
			return null;
		int min = Integer.MAX_VALUE;
		for (int i : c) {
			min = Math.min(min, i);
		}
		return min;
	}

	public static Float min_Float(Collection<Float> c) {
		if (c.size() == 0)
			return null;
		float min = Float.MAX_VALUE;
		for (float i : c) {
			min = Math.min(min, i);
		}
		return min;
	}

	public static Boolean conj(Collection<Boolean> b) {
		if (b.size() == 0)
			return null;
		boolean conj = true;
		for (boolean v : b) {
			conj = conj && v;
		}
		return conj;
	}

	public static Boolean disj(Collection<Boolean> b) {
		if (b.size() == 0)
			return null;
		boolean disj = false;
		for (boolean v : b) {
			disj = disj || v;
		}
		return disj;
	}

	public static String concat(Collection<String> c) {
		if (c.size() == 0)
			return null;
		StringBuffer sb = new StringBuffer();
		for (String s : c) {
			sb.append(s);
		}
		return sb.toString();
	}

	public static <E> Integer count(Collection<E> c) {
		return c.size();
	}

	public static <E> Integer count(E c) {
		return c == null ? 0 : 1;
	}

	// logic expressions

	public static Boolean not(Boolean e) {
		return e == null ? null : !e;
	}

	public static Boolean lt(Integer i, Integer j) {
		return i != null && j != null ? i < j : null;
	}

	public static Boolean lt(Float i, Float j) {
		return i != null && j != null ? i < j : null;
	}

	public static Boolean lte(Integer i, Integer j) {
		return i != null && j != null ? i <= j : null;
	}

	public static Boolean lte(Float i, Float j) {
		return i != null && j != null ? i <= j : null;
	}

	public static Boolean gt(Integer i, Integer j) {
		return i != null && j != null ? i > j : null;
	}

	public static Boolean gt(Float i, Float j) {
		return i != null && j != null ? i > j : null;
	}

	public static Boolean gte(Integer i, Integer j) {
		return i != null && j != null ? i >= j : null;
	}

	public static Boolean gte(Float i, Float j) {
		return i != null && j != null ? i >= j : null;
	}

	public static Boolean and(Boolean i, Boolean j) {
		return i != null && j != null ? i && j : null;
	}

	public static Boolean or(Boolean i, Boolean j) {
		return i != null && j != null ? i || j : null;
	}

	// logic expressions : equality

	public static <E> Boolean eq(E i, E j) {
		return i == null || j == null ? null : i.equals(j);
	}

	public static <E> Boolean eq(E i, Collection<E> j) {
		return i == null || j.size() == 0 ? null : toCollection(i).equals(j);
	}

	public static <E> Boolean eq(Collection<E> i, E j) {
		return i.size() == 0 || j == null ? null : toCollection(j).equals(i);
	}

	public static <E> Boolean eq(Collection<E> i, Collection<E> j) {
		return i.size() == 0 || j.size() == 0 ? null : i.equals(j);
	}

	public static <E> Boolean neq(E i, E j) {
		return i == null || j == null ? null : !i.equals(j);
	}

	public static <E> Boolean neq(E i, Collection<E> j) {
		return i == null || j.size() == 0 ? null : !toCollection(i).equals(j);
	}

	public static <E> Boolean neq(Collection<E> i, E j) {
		return i.size() == 0 || j == null ? null : !toCollection(j).equals(i);
	}

	public static <E> Boolean neq(Collection<E> i, Collection<E> j) {
		return i.size() == 0 || j.size() == 0 ? null : !i.equals(j);
	}

	// logic expressions : conditional

	public static <E> E conditional(Boolean b, E i, E j) {
		return b == null ? null : b ? i : j;
	}

	public static <E> Collection<E> conditional(Boolean b, E i, Collection<E> j) {
		Collection<E> c = emptyCollection();
		return b == null ? c : b ? toCollection(i) : j;
	}

	public static <E> Collection<E> conditional(Boolean b, Collection<E> i, E j) {
		Collection<E> c = emptyCollection();
		return b == null ? c : b ? i : toCollection(j);
	}

	public static <E> Collection<E> conditional(Boolean b, Collection<E> i,
			Collection<E> j) {
		Collection<E> c = emptyCollection();
		return b == null ? c : b ? i : j;
	}

	// cast expressions

	public static Float asFloat(Integer i) {
		return i == null ? null : (float) i;
	}

	public static Collection<Float> asFloat(Collection<Integer> is) {
		Collection<Float> c = emptyCollection();
		for (int i : is) {
			c.add((float) i);
		}
		return c;
	}

	public static Integer asInteger(Float i) {
		return i == null ? null : (int) (float) i;
	}

	public static Collection<Integer> asInteger(Collection<Float> is) {
		Collection<Integer> c = emptyCollection();
		for (float i : is) {
			c.add((int) i);
		}
		return c;
	}

	public static String asString(Object i) {
		return i == null ? null : i.toString();
	}

	public static Collection<String> asString(Collection<Object> is) {
		Collection<String> c = emptyCollection();
		for (Object i : is) {
			c.add(i.toString());
		}
		return c;
	}

}
