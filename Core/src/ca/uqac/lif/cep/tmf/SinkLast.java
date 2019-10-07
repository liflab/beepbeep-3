package ca.uqac.lif.cep.tmf;

import java.util.Queue;

import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.cep.SingleProcessor;

public class SinkLast extends Sink
{
	/*@ non_null @*/ protected Object[] m_last;
	
	protected boolean m_isEmpty;
	
	public SinkLast(int arity)
	{
		super(arity);
		m_last = new Object[arity];
		m_isEmpty = true;
		m_queryable = new ProcessorQueryable(toString(), arity, 0);
	}
	
	public SinkLast()
	{
		this(1);
	}
	
	/*@ pure @*/ public Object getLast(int index)
	{
		return m_last[index];
	}
	
	/*@ pure @*/ public Object getLast()
	{
		return getLast(0);
	}
	
	/*@ pure @*/ public boolean isEmpty()
	{
		return m_isEmpty;
	}

	@Override
	/*@ pure @*/ public SingleProcessor duplicate(boolean with_state)
	{
		SinkLast sl = new SinkLast(getInputArity());
		return copyInto(sl, with_state);
	}
	
	@Override
	/*@ pure @*/ public SingleProcessor copyInto(SingleProcessor p, boolean with_state)
	{
		p = super.copyInto(p, with_state);
		if (with_state)
		{
			for (int i = 0; i < m_last.length; i++)
			{
				((SinkLast) p).m_last[i] = m_last[i];
			}
			((SinkLast) p).m_isEmpty = m_isEmpty;
		}
		return p;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		m_last = inputs;
		m_isEmpty = false;
		return true;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		for (int i = 0; i < m_last.length; i++)
		{
			m_last[i] = null;
		}
		m_isEmpty = true;
	}

	@Override
	protected SingleProcessor readState(Object state, int in_arity, int out_arity) throws ReadException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected Object printState() {
		// TODO Auto-generated method stub
		return null;
	}
}
