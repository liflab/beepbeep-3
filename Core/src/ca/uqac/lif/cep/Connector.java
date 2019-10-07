package ca.uqac.lif.cep;

import ca.uqac.lif.cep.Processor.ProcessorException;
import ca.uqac.lif.cep.Typed.Variant;

public class Connector
{	
	public static boolean CHECK_TYPES = true;

	private Connector()
	{
		super();
	}

	public static void connect(Processor p1, int i1, Processor p2, int i2)
	{
		try
		{
			Pullable p1i1 = p1.getPullableOutput(i1);
			Pushable p2i2 = p2.getPushableInput(i2);
			if (CHECK_TYPES)
			{
				Class<?> p2i2t = p2i2.getType();
				Class<?> p1i1t = p1i1.getType();
				if (p2i2t != null && p1i1t != null && p2i2t != Variant.class && 
						p1i1t != Variant.class && !p2i2t.isAssignableFrom(p1i1t)) 
				{
					throw new ConnectorException("Incompatible types between output " + 
							i1 + " of processor " + p1 + " and input " + i2 + " of processor " + p2);
				}
			}
			p2.setPullableInput(i2, p1i1);
			p1.setPushableOutput(i1, p2i2);
		}
		catch (ProcessorException e)
		{
			throw new ConnectorException(e);
		}
	}

	public static void connect(Processor p1, Processor p2)
	{
		for (int i = 0; i < p1.getOutputArity(); i++)
		{
			connect(p1, i, p2, i);
		}
	}

	public static class ConnectorException extends RuntimeException
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;

		public ConnectorException(Throwable t)
		{
			super(t);
		}

		public ConnectorException(String message)
		{
			super(message);
		}
	}
}