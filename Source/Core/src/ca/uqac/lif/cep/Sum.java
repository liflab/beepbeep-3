package ca.uqac.lif.cep;

import java.util.Vector;

public class Sum extends Combiner
{
	public Sum(int arity)
	{
		super(arity, arity);
	}

	@Override
	protected Vector<Object> initialize()
	{
		int o_arity = getOutputArity();
		Vector<Object> out = new Vector<Object>(o_arity);
		for (int i = 0; i < o_arity; i++)
		{
			out.add(0);
		}
		return out;
	}

	@Override
	protected Vector<Object> combine(Vector<Object> inputs, Vector<Object> total)
	{
		int o_arity = getOutputArity();
		Vector<Object> out = new Vector<Object>(o_arity);
		for (int i = 0; i < o_arity; i++)
		{
			Number n1 = (Number) inputs.get(i);
			Number n2 = (Number) total.get(i);
			out.add(n1.floatValue() + n2.floatValue());
		}
		return out;
		
	}

}
