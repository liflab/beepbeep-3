package ca.uqac.lif.cep.sets;

import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.UnaryFunction;

public class ApplyAll extends UnaryFunction<Multiset,Multiset> 
{
	/**
	 * The function to apply on each element
	 */
	protected Function m_function;
	
	public ApplyAll() 
	{
		super(Multiset.class, Multiset.class);
	}
	
	public ApplyAll(Function function)
	{
		this();
		m_function = function;
	}
	
	/**
	 * Sets the function to apply on each element
	 * @param function The condition
	 */
	public void setCondition(Function function)
	{
		m_function = function;
	}

	@Override
	public Multiset getValue(Multiset x) 
	{
		Multiset out = new Multiset();
		for (Object o : x)
		{
			Object[] in = new Object[1];
			in[0] = o;
			Object[] values = m_function.evaluate(in);
			out.add(values[0]);
		}
		return out;
	}
	
	

}
