package ca.uqac.lif.cep;

import ca.uqac.lif.azrael.Printable;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.Trackable;
import ca.uqac.lif.petitpoucet.circuit.CircuitElement;
import ca.uqac.lif.petitpoucet.common.NthOf;

public interface Processor extends CircuitElement, Contextualizable, Printable, Readable, Startable, StateDuplicable<Processor>, Trackable
{
	public Pushable getPushableInput(int index);
	
	public Pushable getPushableInput();
	
	public Pullable getPullableOutput(int index);
	
	public Pullable getPullableOutput();
	
	public void setPullableInput(int index, Pullable p);
	
	public void setPushableOutput(int index, Pushable p);
	
	public void reset();
		
	public class ProcessorException extends RuntimeException
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;
		
		public ProcessorException(Throwable t)
		{
			super(t);
		}
		
		public ProcessorException(String message)
		{
			super(message);
		}
	}
	
	public class NthEvent extends NthOf
	{
		public NthEvent(int index)
		{
			super(index);
		}
		
		@Override
		public boolean appliesTo(Object o)
		{
			return o instanceof Processor;
		}

		@Override
		public Designator peek()
		{
			return this;
		}

		@Override
		public Designator tail() 
		{
			return null;
		}
		
		@Override
		public String toString()
		{
			return "Event " + m_index;
		}
	}
}
