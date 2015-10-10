package ca.uqac.lif.cep;

import java.util.Queue;

public class Constant extends SingleProcessor
{
	private final Object m_toReturn;

	public Constant(Object o)
	{
		super(0, 1);
		m_toReturn = o;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		return wrapObject(m_toReturn);
	}

}
