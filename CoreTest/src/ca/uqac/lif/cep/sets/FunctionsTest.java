package ca.uqac.lif.cep.sets;

import static org.junit.Assert.*;

import java.util.HashSet;

import org.junit.Test;

/**
 * Unit tests for set functions
 * @author Sylvain Hallé
 *
 */
public class FunctionsTest
{
	@Test
	public void testCardinalitySet1()
	{
		int card = -1;
		HashSet<Integer> set = new HashSet<Integer>();
		card = Cardinality.instance.getValue(set);
		assertEquals(0, card);
		set.add(1);
		card = Cardinality.instance.getValue(set);
		assertEquals(1, card);
		set.add(1);
		card = Cardinality.instance.getValue(set);
		assertEquals(1, card);
	}
	
	@Test
	public void testCardinalityMultiset1()
	{
		int card = -1;
		Multiset set = new Multiset();
		card = Cardinality.instance.getValue(set);
		assertEquals(0, card);
		set.add(1);
		card = Cardinality.instance.getValue(set);
		assertEquals(1, card);
		set.add(1);
		card = Cardinality.instance.getValue(set);
		assertEquals(2, card);
	}
}
