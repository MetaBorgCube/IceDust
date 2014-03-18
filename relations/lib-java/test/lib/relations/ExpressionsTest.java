package lib.relations;

import static org.junit.Assert.*;

import org.junit.Test;

public class ExpressionsTest {

	@Test
	public void testToCollection() {
		assertEquals(Expressions.toCollection(4).size(), 1);
	}

}
