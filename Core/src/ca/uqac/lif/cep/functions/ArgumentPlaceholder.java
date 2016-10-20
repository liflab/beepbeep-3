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

import ca.uqac.lif.cep.Context;

/**
 * Symbol standing for the <i>i</i>-th trace given as input
 * @author Sylvain Hallé
 */
public class ArgumentPlaceholder extends Function
{
	/**
	 * The index of this placeholder
	 */
	private final int m_index;

	/**
	 * Creates a new trace placeholder
	 * @param index The index of the trace this placeholder represents
	 */
	public ArgumentPlaceholder(int index)
	{
		super();
		m_index = index;
	}

	/**
	 * Creates a new trace placeholder, standing for the first
	 * input trace (i.e. index 0)
	 */
	public ArgumentPlaceholder()
	{
		this(0);
	}

	/**
	 * Gets the name of this placeholder
	 * @return The name
	 */
	public int getIndex()
	{
		return m_index;
	}

	@Override
	public int hashCode()
	{
		return m_index;
	}

	@Override
	public boolean equals(Object o)
	{
		if (o == null || !(o instanceof ArgumentPlaceholder))
		{
			return false;
		}
		return m_index == ((ArgumentPlaceholder) o).m_index;
	}
	
	@Override
	public Object[] evaluate(Object[] inputs, Context context)
	{
		Object[] out = new Object[1];
		out[0] = inputs[m_index];;
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
		ArgumentPlaceholder aph = new ArgumentPlaceholder(m_index);
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
		return null;
	}
	
	@Override
	public String toString()
	{
		return "&" + m_index;
	}
}
