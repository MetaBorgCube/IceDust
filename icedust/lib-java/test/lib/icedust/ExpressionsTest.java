package lib.icedust;

import static org.junit.Assert.*;

import java.util.Collection;

import javax.lang.model.type.NullType;

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
        
        assertEquals(new Integer(4), Expressions.choice_One_One(4, 3));
        assertEquals(new Integer(3), Expressions.choice_One_One(singleMultZero, 3));
        assertEquals(singleMultZero, Expressions.choice_One_One(singleMultZero, singleMultZero));
        
        assertEquals(Expressions.toCollection(new Integer(5)), Expressions.choice_Many_One(manyMultZero, 5));
        assertEquals(0, Expressions.choice_Many_One(manyMultZero, singleMultZero).size());
        
        assertEquals(Expressions.toCollection(new Integer(6)), Expressions.choice_One_Many(6, manyMultZero));
        assertEquals(0, Expressions.choice_One_Many(singleMultZero, manyMultZero).size());
        
        assertEquals(0, Expressions.choice_Many_Many(manyMultZero, manyMultZero).size());
        assertEquals(Expressions.toCollection(new Integer(7)), Expressions.choice_Many_Many(Expressions.toCollection(new Integer(7)), manyMultZero));
        assertEquals(Expressions.toCollection(new Integer(8)), Expressions.choice_Many_Many(manyMultZero, Expressions.toCollection(new Integer(8))));
    }
    
    @Test
    public void testMerge() {
        Integer singleMultZero = null;
        Collection<Integer> manyMultZero = Expressions.emptyCollection();
        
        assertEquals(2, Expressions.merge_One_One(4, 3).size());
        assertEquals(1, Expressions.merge_One_One(singleMultZero, 3).size());
        assertEquals(0, Expressions.merge_One_One(singleMultZero, singleMultZero).size());
        
        assertEquals(Expressions.toCollection(new Integer(5)), Expressions.merge_Many_One(manyMultZero, 5));
        assertEquals(0, Expressions.merge_Many_One(manyMultZero, singleMultZero).size());
        
        assertEquals(Expressions.toCollection(new Integer(6)), Expressions.merge_One_Many(6, manyMultZero));
        assertEquals(0, Expressions.merge_One_Many(singleMultZero, manyMultZero).size());
        
        assertEquals(0, Expressions.merge_Many_Many(manyMultZero, manyMultZero).size());
        assertEquals(Expressions.toCollection(new Integer(7)), Expressions.merge_Many_Many(Expressions.toCollection(new Integer(7)), manyMultZero));
        assertEquals(Expressions.toCollection(new Integer(8)), Expressions.merge_Many_Many(manyMultZero, Expressions.toCollection(new Integer(8))));
    }
    
    @Test
    public void testDiv() {
        assertEquals(3, Expressions.div_Integer(6, 2).intValue());
        assertEquals(null, Expressions.div_Integer((NullType)null, 2));
        assertEquals(null, Expressions.div_Integer(6, (NullType)null));
        assertEquals(null, Expressions.div_Integer(6, 0));
    }    
    
    @Test
    public void testCast() {
        assertEquals("3", Expressions.asString(3));
        assertEquals(3.0f, Expressions.asFloat(3).floatValue(),0.000001f);
        assertEquals(3, Expressions.asInteger(3.0f).intValue());
    }    
    
    @Test
    public void testDatetime() {
        assertEquals(3600, Expressions.minus_Date(Expressions.parseDatetime("2015-1-1 9:45:00"), Expressions.parseDatetime("2015-1-1 8:45:00")).intValue());
    }

}
