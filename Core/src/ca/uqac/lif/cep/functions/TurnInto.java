package ca.uqac.lif.cep.functions;

import java.util.ArrayList;
import java.util.List;
import java.util.Queue;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;

public class TurnInto extends SingleProcessor
{
	/*@ non_null @*/ protected Object[] m_value;
	
	public TurnInto(Object ... value)
	{
		super(value.length, value.length);
		m_value = value;
	}

	@Override
	public Processor duplicate(boolean with_state) 
	{
		TurnInto ti = new TurnInto(m_value);
		return copyInto(ti, with_state);
	}

	@Override
	public boolean compute(Object[] inputs, Queue<Object[]> outputs) 
	{
		outputs.add(m_value);
		return true;
	}

	@Override
	protected SingleProcessor readState(Object state, int in_arity, int out_arity) throws ReadException 
	{
		if (!(state instanceof List))
		{
			throw new ReadException("Unexpected object");
		}
		List<?> value = (List<?>) state;
		return new TurnInto(value.toArray());
	}

	@Override
	protected Object printState() 
	{
		List<Object> value = new ArrayList<Object>(m_value.length);
		for (Object o : m_value)
		{
			value.add(o);
		}
		return value;
	}
}
