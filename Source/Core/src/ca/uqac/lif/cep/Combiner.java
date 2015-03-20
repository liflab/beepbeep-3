package ca.uqac.lif.cep;

import java.util.Vector;

public abstract class Combiner extends Processor
{
	protected Vector<Object> m_total;
	
	public Combiner(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
		m_total = initialize();
	}

	@Override
	protected Vector<Object> compute(Vector<Object> inputs)
	{
		m_total = combine(inputs, m_total);
		return m_total;
	}
	
	protected abstract Vector<Object> initialize();
	
	protected abstract Vector<Object> combine(Vector<Object> inputs, Vector<Object> total);

}
