package ca.uqac.lif.cep.sets;

import java.util.List;

import ca.uqac.lif.cep.functions.UnaryFunction;

public class NthElement extends UnaryFunction<Object,Object>
{
	/**
	 * The position of the element to get
	 */
	protected int m_n;
	
	public NthElement(int n) 
	{
		super(Object.class, Object.class);
		m_n = n;
	}

	@Override
	public Object getValue(Object x) 
	{
		if (x instanceof Object[])
		{
			Object[] array = (Object[]) x;
			return array[m_n];
		}
		if (x instanceof List<?>)
		{
			List<?> list = (List<?>) x;
			if (m_n < list.size())
			{
				return list.get(m_n);
			}
		}
		return null;
	}
	
	@Override
	public NthElement clone()
	{
		return new NthElement(m_n);
	}

	@Override
	public String toString()
	{
		return m_n + "th of ";
	}
}
