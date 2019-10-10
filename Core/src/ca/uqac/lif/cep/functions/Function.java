package ca.uqac.lif.cep.functions;

import ca.uqac.lif.azrael.Printable;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.StateDuplicable;

public interface Function extends Printable, Readable, StateDuplicable<Function>
{
	public FunctionQueryable evaluate(Object[] inputs, Object[] outputs, Context c);
	
	public FunctionQueryable evaluate(Object[] inputs, Object[] outputs);
	
	public Class<?> getInputType(int index);
	
	public Class<?> getOutputType(int index);
	
	public int getInputArity();
	
	public int getOutputArity();
	
	public void reset();
	
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
