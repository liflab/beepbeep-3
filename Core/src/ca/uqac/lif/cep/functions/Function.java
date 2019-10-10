package ca.uqac.lif.cep.functions;

import ca.uqac.lif.azrael.Printable;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Contextualizable;
import ca.uqac.lif.cep.StateDuplicable;
import ca.uqac.lif.petitpoucet.Trackable;
import ca.uqac.lif.petitpoucet.circuit.CircuitElement;

public interface Function extends CircuitElement, Contextualizable, Printable, Readable, StateDuplicable<Function>, Trackable
{
	public Object getOutput(int index);
	
	public Object getOutput();
	
	public void reset();
	
	public FunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c);
	
	public FunctionQueryable evaluate(Object[] inputs, Object[] outputs);
	
	public Class<?> getInputType(int index);
	
	public Class<?> getOutputType(int index);
	
	public class FunctionException extends RuntimeException
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 2L;
		
		public FunctionException(Throwable t)
		{
			super(t);
		}
		
		public FunctionException(String message)
		{
			super(message);
		}
	}
}
