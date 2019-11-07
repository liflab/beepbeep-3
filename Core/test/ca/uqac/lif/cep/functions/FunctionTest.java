package ca.uqac.lif.cep.functions;

import org.junit.Test;

import ca.uqac.lif.petitpoucet.functions.Function.FunctionException;

public class FunctionTest
{
	@Test(expected = FunctionException.class)
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
			throw new FunctionException(e);
		}
	}

	@Test(expected = FunctionException.class)
	public void testExceptionString()
	{
		throw new FunctionException("foo");
	}
}
