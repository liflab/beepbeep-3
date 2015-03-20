package ca.uqac.lif.cep;

import java.util.Vector;

public class Incrementer extends Processor
{
	protected float m_increment;
	
	public Incrementer(float increment)
	{
		super(1, 1);
		m_increment = increment;
	}

	@Override
	protected Vector<Object> compute(Vector<Object> inputs)
	{
		Vector<Object> outputs = new Vector<Object>();
		for (Object in : inputs)
		{
			if (in instanceof Number)
			{
				Number n = (Number) in;
				n = n.floatValue() + m_increment;
				outputs.add(n);
			}
		}
		return outputs;
	}

}
