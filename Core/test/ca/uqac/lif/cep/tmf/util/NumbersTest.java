package ca.uqac.lif.cep.tmf.util;

import static org.junit.Assert.*;

import org.junit.Test;

import ca.uqac.lif.cep.util.Numbers;

public class NumbersTest 
{
	@Test
	public void testSum1()
	{
		Object[] outputs = new Object[1];
		Numbers.Sum sum = new Numbers.Sum();
		sum.evaluate(new Object[] {1}, outputs);
		assertEquals(1f, outputs[0]);
		sum.evaluate(new Object[] {2}, outputs);
		assertEquals(3f, outputs[0]);
		sum.devaluate(new Object[] {1}, outputs);
		assertEquals(2f, outputs[0]);
	}
}
