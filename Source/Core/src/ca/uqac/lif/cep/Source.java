package ca.uqac.lif.cep;

import java.util.Vector;

public abstract class Source extends Processor
{
	Source(int out_arity)
	{
		super(0, out_arity);
	}
	
	/**
	 * Tells the source to push events into the pipeline
	 */
	public final void push()
	{
		Vector<Object> output = compute(null);
		for (int i = 0; i < output.size(); i++)
		{
			Pushable p = m_outputPushables.get(i);
			p.push(output.get(i));
		}
	}
}
