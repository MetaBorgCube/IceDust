package lib.relations;

import static org.junit.Assert.*;

import java.util.Collection;

import org.junit.Test;

public class ExpressionsTest {

	@Test
	public void testEmptyCollection() {
		assertEquals(0, Expressions.emptyCollection().size());
	}
	
	@Test
	public void testToCollection() {
		assertEquals(Expressions.toCollection(4).size(), 1);
	}
	
	@Test
	public void testChoice() {
		Integer singleMultZero = null;
		Collection<Integer> manyMultZero = Expressions.emptyCollection();
		
		assertEquals(new Integer(4), Expressions.choice(4, 3));
		assertEquals(new Integer(3), Expressions.choice(singleMultZero, 3));
		assertEquals(singleMultZero, Expressions.choice(singleMultZero, singleMultZero));
		
		assertEquals(Expressions.toCollection(new Integer(5)), Expressions.choice(manyMultZero, 5));
		assertEquals(0, Expressions.choice(manyMultZero, singleMultZero).size());
		
		assertEquals(Expressions.toCollection(new Integer(6)), Expressions.choice(6, manyMultZero));
		assertEquals(0, Expressions.choice(singleMultZero, manyMultZero).size());
		
		assertEquals(0, Expressions.choice(manyMultZero, manyMultZero).size());
		assertEquals(Expressions.toCollection(new Integer(7)), Expressions.choice(Expressions.toCollection(new Integer(7)), manyMultZero));
		assertEquals(Expressions.toCollection(new Integer(8)), Expressions.choice(manyMultZero, Expressions.toCollection(new Integer(8))));
	}
	
	@Test
	public void testMerge() {
		Integer singleMultZero = null;
		Collection<Integer> manyMultZero = Expressions.emptyCollection();
		
		assertEquals(2, Expressions.merge(4, 3).size());
		assertEquals(1, Expressions.merge(singleMultZero, 3).size());
		assertEquals(0, Expressions.merge(singleMultZero, singleMultZero).size());
		
		assertEquals(Expressions.toCollection(new Integer(5)), Expressions.merge(manyMultZero, 5));
		assertEquals(0, Expressions.merge(manyMultZero, singleMultZero).size());
		
		assertEquals(Expressions.toCollection(new Integer(6)), Expressions.merge(6, manyMultZero));
		assertEquals(0, Expressions.merge(singleMultZero, manyMultZero).size());
		
		assertEquals(0, Expressions.merge(manyMultZero, manyMultZero).size());
		assertEquals(Expressions.toCollection(new Integer(7)), Expressions.merge(Expressions.toCollection(new Integer(7)), manyMultZero));
		assertEquals(Expressions.toCollection(new Integer(8)), Expressions.merge(manyMultZero, Expressions.toCollection(new Integer(8))));
	}
	
	@Test
	public void testDiv() {
		assertEquals(3, Expressions.div(6, 2).intValue());
		assertEquals(null, Expressions.div(null, 2));
		assertEquals(null, Expressions.div(6, null));
		assertEquals(null, Expressions.div(6, 0));
	}	
	
	@Test
	public void testCast() {
		assertEquals("3", Expressions.asString(3));
		assertEquals(3.0f, Expressions.asFloat(3).floatValue(),0.000001f);
		assertEquals(3, Expressions.asInteger(3.0f).intValue());
	}

}
