package ca.uqac.lif.cep.tmf;

import java.util.ArrayDeque;
import java.util.Queue;

import ca.uqac.lif.cep.SingleProcessor;

public abstract class Source extends SingleProcessor
{
	public Source(int out_arity)
	{
		super(0, out_arity);
	}

	public Source()
	{
		this(1);
	}

	public void push()
	{
		Queue<Object[]> outs = new ArrayDeque<Object[]>();
		compute(null, outs);
		while (!outs.isEmpty())
		{
			Object[] out = outs.remove();
			for (int i = 0; i < m_outputPushables.length; i++)
			{
				m_outputPushables[i].push(out[i]);
			}
		}
	}

	public void end()
	{
		for (int i = 0; i < m_outputPushables.length; i++)
		{
			m_outputPushables[i].end();
		}
	}
}
