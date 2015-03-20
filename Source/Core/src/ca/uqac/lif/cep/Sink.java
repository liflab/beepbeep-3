package ca.uqac.lif.cep;

import java.util.Vector;

public abstract class Sink extends Processor
{
	public Sink(int in_arity)
	{
		super(in_arity, 0);
	}

	/**
	 * Tells the sink to pull events from the pipeline
	 */
	public final void pull()
	{
		Vector<Object> inputs = new Vector<Object>(getInputArity());
		for (int i = 0; i < getInputArity(); i++)
		{
			Pullable p = m_inputPullables.get(i);
			inputs.add(p.pull());
		}
		compute(inputs);
	}

}
