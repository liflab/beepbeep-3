/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published
    by the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep.functions;

import java.util.Set;

import ca.uqac.lif.cep.Connector.Variant;
import ca.uqac.lif.cep.Context;

public class ArgumentPlaceholder extends Function
{
	/**
	 * The name of this placeholder
	 */
	protected final String m_name;

	/**
	 * Creates a new argument placeholder
	 * @param name The name of this placeholder
	 */
	public ArgumentPlaceholder(String name)
	{
		super();
		m_name = name;
	}

	/**
	 * Gets the name of this placeholder
	 * @return The name
	 */
	public String getName()
	{
		return m_name;
	}

	@Override
	public int hashCode()
	{
		return m_name.hashCode();
	}

	@Override
	public boolean equals(Object o)
	{
		if (o == null || !(o instanceof ArgumentPlaceholder))
		{
			return false;
		}
		return m_name.compareTo(((ArgumentPlaceholder) o).m_name) == 0;
	}
	
	@Override
	public Object[] evaluate(Object[] inputs, Context context)
	{
		if (context == null || !context.containsKey(m_name))
		{
			return null;
		}
		Object[] out = new Object[1];
		out[0] = context.get(m_name);
		return out;
	}
	
	@Override
	public Object[] evaluate(Object[] inputs)
	{
		return evaluate(inputs, null);
	}

	@Override
	public int getInputArity()
	{
		return 0;
	}

	@Override
	public int getOutputArity() 
	{
		return 0;
	}

	@Override
	public void reset() 
	{
		// Nothing to do
	}

	@Override
	public ArgumentPlaceholder clone()
	{
		ArgumentPlaceholder aph = new ArgumentPlaceholder(m_name);
		return aph;
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index) 
	{
		// Nothing to do
	}

	@Override
	public Class<?> getOutputTypeFor(int index) 
	{
		return Variant.class;
	}
	
	@Override
	public String toString()
	{
		return "$" + m_name;
	}

}
