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

	public static Integer minus(Integer i, Integer j) {
		return i != null && j != null ? i - j : null;
	}

	public static Integer mul(Integer i, Integer j) {
		return i != null && j != null ? i * j : null;
	}

	public static Integer mod(Integer i, Integer j) {
		return i != null && j != null && j != 0 ? i % j : null;
	}

	public static Integer div(Integer i, Integer j) {
		return i != null && j != null && j != 0 ? i / j : null;
	}

	// aggregation expressions

	public static Integer avg(Collection<Integer> c) {
		if (c.size() == 0)
			return null;
		int sum = 0;
		for (int i : c) {
			sum += i;
		}
		return sum / c.size();
	}

	public static Integer sum(Collection<Integer> c) {
		int sum = 0;
		for (int i : c) {
			sum += i;
		}
		return sum;
	}

	public static Integer max(Collection<Integer> c) {
		if (c.size() == 0)
			return null;
		int max = Integer.MIN_VALUE;
		for (int i : c) {
			max = Math.max(max, i);
		}
		return max;
	}

	public static Integer min(Collection<Integer> c) {
		if (c.size() == 0)
			return null;
		int min = Integer.MAX_VALUE;
		for (int i : c) {
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

	public static Boolean lte(Integer i, Integer j) {
		return i != null && j != null ? i <= j : null;
	}

	public static Boolean gt(Integer i, Integer j) {
		return i != null && j != null ? i > j : null;
	}

	public static Boolean gte(Integer i, Integer j) {
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
		return b == null ? null : b ? toCollection(i) : j;
	}

	public static <E> Collection<E> conditional(Boolean b, Collection<E> i, E j) {
		return b == null ? null : b ? i : toCollection(j);
	}

	public static <E> Collection<E> conditional(Boolean b, Collection<E> i,
			Collection<E> j) {
		return b == null ? null : b ? i : j;
	}

}
