package lib.relations;

import static org.junit.Assert.*;

import java.util.Collection;

import org.junit.Test;

public class ExpressionsTest {

	@Test
	public void testToCollection() {
		assertEquals(Expressions.toCollection(4).size(), 1);
	}
	
	@Test
	public void testChoice() {
		Integer nullInt = null;
		Collection<Integer> nullCol = null;
		assertEquals(new Integer(4), Expressions.choice(4, 3));
		assertEquals(new Integer(3), Expressions.choice(nullInt, 3));
		assertEquals(null, Expressions.choice(nullInt, nullInt));
	}
	
	@Test
	public void testDiv() {
		assertEquals(3, Expressions.div(6, 2).intValue());
		assertEquals(null, Expressions.div(null, 2));
		assertEquals(null, Expressions.div(6, null));
		assertEquals(null, Expressions.div(6, 0));
	}

}
