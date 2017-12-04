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

import ca.uqac.lif.cep.Context;

/**
 * Placeholder for the value of a context element
 * 
 * @author Sylvain Hallé
 */
public class ContextVariable extends Variable
{
	/**
	 * The name of this placeholder
	 */
	protected final String m_name;

	/**
	 * Creates a new argument placeholder
	 * @param name The name of this placeholder
	 */
	public ContextVariable(String name)
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
		if (o == null || !(o instanceof ContextVariable))
		{
			return false;
		}
		return m_name.compareTo(((ContextVariable) o).m_name) == 0;
	}

	@Override
	@SuppressWarnings("squid:S1168")
	public void evaluate(Object[] inputs, Object[] outputs, Context context)
	{
		if (context == null || !context.containsKey(m_name))
		{
			outputs[0] = null;
			return;
		}
		outputs[0] = context.get(m_name);
	}

	@Override
	public ContextVariable duplicate()
	{
		return new ContextVariable(m_name);
	}
	
	@Override
	public String toString()
	{
		return "$" + m_name;
	}

}
