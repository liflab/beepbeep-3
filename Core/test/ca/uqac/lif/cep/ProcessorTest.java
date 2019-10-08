package ca.uqac.lif.cep;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import ca.uqac.lif.cep.Processor.ProcessorException;
import ca.uqac.lif.cep.TestUtilities.TestableSingleProcessor;

public class ProcessorTest
{
	@Test(expected = ProcessorException.class)
	public void testExceptionThrowable()
	{
		Object[] o = new Object[0];
		try
		{
			@SuppressWarnings("unused")
			Object x = o[0];
		}
		catch (ArrayIndexOutOfBoundsException e)
		{
			throw new ProcessorException(e);
		}
	}

	@Test(expected = ProcessorException.class)
	public void testExceptionString()
	{
		throw new ProcessorException("foo");
	}
	
	@Test
	public void testNthEvent()
	{
		Processor.NthEvent ne = new Processor.NthEvent(3);
		assertFalse(ne.appliesTo(3));
		TestableSingleProcessor spw = new TestableSingleProcessor(1, 1);
		assertTrue(ne.appliesTo(spw));
		assertEquals(ne, ne.peek());
		assertNull(ne.tail());
		assertNotNull(ne.toString());
	}

	public static void assertConnectedTo(Processor p1, int i, Processor p2, int j)
	{
		Pushable p1_oi = (Pushable) p1.getOutputConnection(i);
		assertEquals(p2, p1_oi.getObject());
		assertEquals(j, p1_oi.getIndex());
		Pullable p2_ij = (Pullable) p2.getInputConnection(j);
		assertEquals(p1, p2_ij.getObject());
		assertEquals(i, p2_ij.getIndex());
	}

	public static void assertNotConnectedTo(Processor p1, int i, Processor p2, int j)
	{
		try
		{
			Pushable p1_oi = (Pushable) p1.getOutputConnection(i);
			assertEquals(p2, p1_oi.getObject());
			assertEquals(j, p1_oi.getIndex());
			Pullable p2_ij = (Pullable) p2.getInputConnection(j);
			assertEquals(p1, p2_ij.getObject());
			assertEquals(i, p2_ij.getIndex());
		}
		catch (AssertionError e)
		{
			return;
		}
		throw new AssertionError("Objects are connected while they shouldn't");
	}
}
