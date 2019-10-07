package ca.uqac.lif.cep.functions;

import java.util.Queue;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.SingleProcessor;

public class Cumulate extends SingleProcessor
{
	/*@ non_null @*/ protected CumulativeFunction<?> m_function;
	
	public Cumulate(/*@ non_null @*/ CumulativeFunction<?> f)
	{
		super(1, 1);
		m_function = f;
	}

	@Override
	public Cumulate duplicate(boolean with_state) 
	{
		Cumulate c = new Cumulate(m_function.duplicate(with_state));
		return (Cumulate) copyInto(c, with_state);
	}

	@Override
	public boolean compute(Object[] inputs, Queue<Object[]> outputs) 
	{
		Object[] out = new Object[1];
		m_function.evaluate(inputs, out);
		outputs.add(out);
		return true;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_function.reset();
	}

	@Override
	protected SingleProcessor readState(Object state, int in_arity, int out_arity) throws ReadException 
	{
		if (!(state instanceof CumulativeFunction))
		{
			throw new ReadException("Unexpected object");
		}
		return new Cumulate((CumulativeFunction<?>) state);
	}

	@Override
	protected Object printState() 
	{
		return m_function;
	}
}