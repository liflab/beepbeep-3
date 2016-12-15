package ca.uqac.lif.cep.tmf;

import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.cep.util.CacheMap;

public class NamedMapPlaceholder extends UnaryFunction<Object,Object>
{
	protected int m_lastIndex = -1;

	protected String m_name;

	public NamedMapPlaceholder(String name)
	{
		super(Object.class, Object.class);
		m_name = name;
	}

	@Override
	public Object getValue(Object in)
	{
		@SuppressWarnings("unchecked")
		CacheMap<Object> map = (CacheMap<Object>) in;
		Object o = null;
		if (m_lastIndex == -1)
		{
			m_lastIndex = map.getIndexOf(m_name);
		}
		o = map.getValue(m_lastIndex);
		return o;
	}
}
