package lib.relations;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Date;
import javax.lang.model.type.NullType;

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

	public static <E> E choice_One_One(E e1, E e2) {
		return e1 != null ? e1 : e2;
	}

	public static <E> Collection<E> choice_One_Many(E e1, Collection<E> e2) {
		return e1 != null ? toCollection(e1) : e2;
	}

	public static <E> Collection<E> choice_Many_One(Collection<E> e1, E e2) {
		return e1.size() > 0 ? e1 : e2 != null ? toCollection(e2) : e1;
	}

	public static <E> Collection<E> choice_Many_Many(Collection<E> e1, Collection<E> e2) {
		return e1.size() > 0 ? e1 : e2;
	}

	public static <E> Collection<E> merge_One_One(E e1, E e2) {
		Collection<E> c = emptyCollection();
		if (e1 != null)
			c.add(e1);
		if (e2 != null)
			c.add(e2);
		return c;
	}

	public static <E> Collection<E> merge_One_Many(E e1, Collection<E> e2) {
		Collection<E> c = emptyCollection();
		if (e1 != null)
			c.add(e1);
		c.addAll(e2);
		return c;
	}

	public static <E> Collection<E> merge_Many_One(Collection<E> e1, E e2) {
		Collection<E> c = emptyCollection();
		c.addAll(e1);
		if (e2 != null)
			c.add(e2);
		return c;
	}

	public static <E> Collection<E> merge_Many_Many(Collection<E> e1, Collection<E> e2) {
		Collection<E> c = emptyCollection();
		c.addAll(e1);
		c.addAll(e2);
		return c;
	}

	// math expressions

	public static NullType plus_NullType(NullType i, NullType j) {
		return null;
	}
	
	public static String plus_String(NullType i, String j) {
		return null;
	}
	
	public static String plus_String(String i, NullType j) {
		return null;
	}
	
	public static Integer plus_Integer(NullType i, Integer j) {
		return null;
	}
	
	public static Integer plus_Integer(Integer i, NullType j) {
		return null;
	}	
	
	public static Float plus_Float(NullType i, Float j) {
		return null;
	}
	
	public static Float plus_Float(Float i, NullType j) {
		return null;
	}
	
	public static String plus_String(String i, String j) {
		return i != null && j != null ? i + j : null;
	}

	public static Integer plus_Integer(Integer i, Integer j) {
		return i != null && j != null ? i + j : null;
	}

	public static Float plus_Float(Float i, Float j) {
		return i != null && j != null ? i + j : null;
	}
	
	public static NullType minus_NullType(NullType i, NullType j) {
		return null;
	}
	
	public static Integer minus_Integer(NullType i, Integer j) {
		return null;
	}
	
	public static Integer minus_Integer(Integer i, NullType j) {
		return null;
	}	
	
	public static Float minus_Float(NullType i, Float j) {
		return null;
	}
	
	public static Float minus_Float(Float i, NullType j) {
		return null;
	}

	public static Integer minus_Date(NullType i, Date j) {
		return null;
	}

	public static Integer minus_Date(Date i, NullType j) {
		return null;
	}

	public static Integer minus_Integer(Integer i, Integer j) {
		return i != null && j != null ? i - j : null;
	}

	public static Float minus_Float(Float i, Float j) {
		return i != null && j != null ? i - j : null;
	}

	public static Integer minus_Date(Date i, Date j) {
		return i != null && j != null ? (int) ((i.getTime() - j.getTime()) / 1000)
				: null;
	}
	
	public static NullType mul_NullType(NullType i, NullType j) {
		return null;
	}
	
	public static Integer mul_Integer(NullType i, Integer j) {
		return null;
	}
	
	public static Integer mul_Integer(Integer i, NullType j) {
		return null;
	}	
	
	public static Float mul_Float(NullType i, Float j) {
		return null;
	}
	
	public static Float mul_Float(Float i, NullType j) {
		return null;
	}

	public static Integer mul_Integer(Integer i, Integer j) {
		return i != null && j != null ? i * j : null;
	}

	public static Float mul_Float(Float i, Float j) {
		return i != null && j != null ? i * j : null;
	}
	
	public static NullType mod_NullType(NullType i, NullType j) {
		return null;
	}
	
	public static Integer mod_Integer(NullType i, Integer j) {
		return null;
	}
	
	public static Integer mod_Integer(Integer i, NullType j) {
		return null;
	}	
	
	public static Float mod_Float(NullType i, Float j) {
		return null;
	}
	
	public static Float mod_Float(Float i, NullType j) {
		return null;
	}

	public static Integer mod_Integer(Integer i, Integer j) {
		return i != null && j != null && j != 0 ? i % j : null;
	}

	public static Float mod_Float(Float i, Float j) {
		return i != null && j != null && j != 0 ? i % j : null;
	}
	
	public static NullType div_NullType(NullType i, NullType j) {
		return null;
	}
	
	public static Integer div_Integer(NullType i, Integer j) {
		return null;
	}
	
	public static Integer div_Integer(Integer i, NullType j) {
		return null;
	}	
	
	public static Float div_Float(NullType i, Float j) {
		return null;
	}
	
	public static Float div_Float(Float i, NullType j) {
		return null;
	}

	public static Float div_Integer(Integer i, Integer j) {
		return i != null && j != null && j != 0 ? (float)i / (float)j : null;
	}

	public static Float div_Float(Float i, Float j) {
		return i != null && j != null && j != 0 ? i / j : null;
	}
	
	public static NullType floordiv_NullType(NullType i, NullType j) {
		return null;
	}
	
	public static Integer floordiv_Integer(NullType i, Integer j) {
		return null;
	}
	
	public static Integer floordiv_Integer(Integer i, NullType j) {
		return null;
	}	
	
	public static Float floordiv_Float(NullType i, Float j) {
		return null;
	}
	
	public static Float floordiv_Float(Float i, NullType j) {
		return null;
	}
	
	public static Integer floordiv_Integer(Integer i, Integer j) {
		return i != null && j != null && j != 0 ? i / j : null;
	}

	public static Float floordiv_Float(Float i, Float j) {
		return i != null && j != null && j != 0 ? (float)Math.floor(i / j) : null;
	}

	// aggregation expressions

	public static NullType avg_NullType(NullType i, NullType j) {
		return null;
	}
	
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

	public static NullType sum_NullType(NullType i, NullType j) {
		return null;
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

	public static NullType max_NullType(NullType i, NullType j) {
		return null;
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

	public static NullType min_NullType(NullType i, NullType j) {
		return null;
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
		boolean conj = true;
		for (boolean v : b) {
			conj = conj && v;
		}
		return conj;
	}

	public static Boolean disj(Collection<Boolean> b) {
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

	public static Boolean not_Boolean(Boolean e) {
		return e == null ? null : !e;
	}

	public static NullType lt_NullType(NullType i, NullType j) {
		return null;
	}
	
	public static Boolean lt_Integer(Integer i, Integer j) {
		return i != null && j != null ? i < j : null;
	}

	public static Boolean lt_Float(Float i, Float j) {
		return i != null && j != null ? i < j : null;
	}

	public static Boolean lt_Date(Date i, Date j) {
		return i != null && j != null ? i.compareTo(j) < 0 : null;
	}

	public static NullType lte_NullType(NullType i, NullType j) {
		return null;
	}

	public static Boolean lte_Integer(Integer i, Integer j) {
		return i != null && j != null ? i <= j : null;
	}

	public static Boolean lte_Float(Float i, Float j) {
		return i != null && j != null ? i <= j : null;
	}

	public static Boolean lte_Date(Date i, Date j) {
		return i != null && j != null ? i.compareTo(j) <= 0 : null;
	}

	public static NullType gt_NullType(NullType i, NullType j) {
		return null;
	}

	public static Boolean gt_Integer(Integer i, Integer j) {
		return i != null && j != null ? i > j : null;
	}

	public static Boolean gt_Float(Float i, Float j) {
		return i != null && j != null ? i > j : null;
	}

	public static Boolean gt_Date(Date i, Date j) {
		return i != null && j != null ? i.compareTo(j) > 0 : null;
	}

	public static NullType gte_NullType(NullType i, NullType j) {
		return null;
	}
	
	public static Boolean gte_Integer(Integer i, Integer j) {
		return i != null && j != null ? i >= j : null;
	}

	public static Boolean gte_Float(Float i, Float j) {
		return i != null && j != null ? i >= j : null;
	}

	public static Boolean gte_Date(Date i, Date j) {
		return i != null && j != null ? i.compareTo(j) >= 0 : null;
	}
	
	public static Boolean and(Boolean i, Boolean j) {
		return i != null && j != null ? i && j : null;
	}

	public static Boolean or(Boolean i, Boolean j) {
		return i != null && j != null ? i || j : null;
	}

	// logic expressions : equality

	public static <E> Boolean eq_One_One(E i, E j) {
		return i == null || j == null ? null : i.equals(j);
	}

	public static <E> Boolean eq_One_Many(E i, Collection<E> j) {
		return i == null || j.size() == 0 ? null : toCollection(i).equals(j);
	}

	public static <E> Boolean eq_Many_One(Collection<E> i, E j) {
		return i.size() == 0 || j == null ? null : toCollection(j).equals(i);
	}

	public static <E> Boolean eq_Many_Many(Collection<E> i, Collection<E> j) {
		return i.size() == 0 || j.size() == 0 ? null : i.equals(j);
	}

	public static <E> Boolean neq_One_One(E i, E j) {
		return i == null || j == null ? null : !i.equals(j);
	}

	public static <E> Boolean neq_One_Many(E i, Collection<E> j) {
		return i == null || j.size() == 0 ? null : !toCollection(i).equals(j);
	}

	public static <E> Boolean neq_Many_One(Collection<E> i, E j) {
		return i.size() == 0 || j == null ? null : !toCollection(j).equals(i);
	}

	public static <E> Boolean neq_Many_Many(Collection<E> i, Collection<E> j) {
		return i.size() == 0 || j.size() == 0 ? null : !i.equals(j);
	}

	// logic expressions : conditional

	public static <E> E conditional_One_One_One(Boolean b, E i, E j) {
		return b == null ? null : b ? i : j;
	}

	public static <E> Collection<E> conditional_One_One_Many(Boolean b, E i, Collection<E> j) {
		Collection<E> c = emptyCollection();
		return b == null ? c : b ? toCollection(i) : j;
	}

	public static <E> Collection<E> conditional_One_Many_One(Boolean b, Collection<E> i, E j) {
		Collection<E> c = emptyCollection();
		return b == null ? c : b ? i : toCollection(j);
	}

	public static <E> Collection<E> conditional_One_Many_Many(Boolean b, Collection<E> i, Collection<E> j) {
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

	// literals

	public static Date parseDatetime(String s) {
		try {
			return new SimpleDateFormat("yyyy-MM-dd H:mm:ss").parse(s);
		} catch (ParseException e) {
			return null;
		}
	}

}
