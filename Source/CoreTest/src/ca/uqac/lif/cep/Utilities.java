package ca.uqac.lif.cep;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Queue;

import org.junit.Test;

public class Utilities 
{
	@Test
	public void dummyTest()
	{
		// Dummy test, just so JUnit won't complain about a class
		// that has no test in it
	}
	
	public static void queueContains(int value, Queue<Object> queue)
	{
		assertEquals(1, queue.size());
		Object o = queue.remove();
		assertNotNull(o);
		assertTrue(o instanceof Number);
		assertEquals(value, ((Number) o).intValue());
	}
}
