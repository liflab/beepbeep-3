package ca.uqac.lif.cep;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.Printable;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.Readable;

public class Context implements Map<String,Object>, Printable, Readable
{
	/*@ non_null @*/ private final Map<String,Object> m_map;

	public Context()
	{
		super();
		m_map = new HashMap<String,Object>();
	}

	@Override
	public int size() 
	{
		return m_map.size();
	}

	@Override
	public boolean isEmpty()
	{
		return m_map.isEmpty();
	}

	@Override
	public boolean containsKey(Object key)
	{
		return m_map.containsKey(key);
	}

	@Override
	public boolean containsValue(Object value) 
	{
		return m_map.containsValue(value);
	}

	@Override
	public Object get(Object key) 
	{
		return m_map.get(key);
	}

	@Override
	public Object put(String key, Object value)
	{
		return m_map.put(key, value);
	}

	@Override
	public Object remove(Object key)
	{
		return m_map.remove(key);
	}

	@Override
	public void putAll(Map<? extends String, ? extends Object> m)
	{
		m_map.putAll(m);
	}

	@Override
	public void clear()
	{
		m_map.clear();
	}

	@Override
	public Set<String> keySet()
	{
		return m_map.keySet();
	}

	@Override
	public Collection<Object> values() 
	{
		return m_map.values();
	}

	@Override
	public Set<Entry<String, Object>> entrySet() 
	{
		return m_map.entrySet();
	}

	@SuppressWarnings("unchecked")
	@Override
	public Context read(ObjectReader<?> reader, Object o) throws ReadException
	{
		Object r_o = reader.read(o);
		if (!(r_o instanceof Map))
		{
			throw new ReadException("Unexpected object");
		}
		Context c = new Context();
		c.putAll((Map<String,Object>) r_o);
		return c;
	}

	@Override
	public Object print(ObjectPrinter<?> printer) throws PrintException 
	{
		Map<String,Object> map = new HashMap<String,Object>(size());
		map.putAll(this);
		return printer.print(map);
	}
}