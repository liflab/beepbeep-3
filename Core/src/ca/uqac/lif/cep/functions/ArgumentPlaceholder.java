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
 * Symbol standing for the <i>i</i>-th trace given as input
 * @author Sylvain Hallé
 */
public class ArgumentPlaceholder extends Placeholder
{
	/**
	 * The index of this placeholder
	 */
	protected final int m_index;
	
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
	public void evaluate(Object[] inputs, Object[] outputs, Context context)
	{
		outputs[0] = inputs[m_index];
	}

	@Override
	public ArgumentPlaceholder duplicate()
	{
		return this;
	}
	
	@Override
	public String toString()
	{
		return "$" + m_index;
	}
}
