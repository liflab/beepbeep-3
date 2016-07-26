package ca.uqac.lif.cep.sets;

import ca.uqac.lif.cep.functions.UnaryFunction;

public class GetElements extends UnaryFunction<Multiset,Multiset> 
{
	/**
	 * The condition to evaluate on each element
	 */
	protected UnaryFunction<Object,Boolean> m_condition;
	
	public GetElements() 
	{
		super(Multiset.class, Multiset.class);
	}
	
	public GetElements(UnaryFunction<Object,Boolean> condition)
	{
		this();
		m_condition = condition;
	}
	
	/**
	 * Sets the condition to evaluate on each element
	 * @param condition The condition
	 */
	public void setCondition(UnaryFunction<Object,Boolean> condition)
	{
		m_condition = condition;
	}

	@Override
	public Multiset getValue(Multiset x) 
	{
		Multiset out = new Multiset();
		for (Object o : x)
		{
			Object[] in = new Object[1];
			in[0] = o;
			Object[] values = m_condition.evaluate(in);
			if (values[0] instanceof Boolean && ((Boolean) values[0]))
			{
				out.add(o);
			}
		}
		return out;
	}
	
	

}
