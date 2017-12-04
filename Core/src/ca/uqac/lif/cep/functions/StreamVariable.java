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
public class StreamVariable extends Variable
{
	/**
	 * A variable standing for the first input stream
	 * (i.e. argument number 0). It is recommended to reuse this
	 * instance everywhere the first argument is referred to in
	 * a function.
	 */
	public static final StreamVariable X = new StreamVariable(0);
	
	/**
	 * A variable standing for the second input stream
	 * (i.e. argument number 1). It is recommended to reuse this
	 * instance everywhere the first argument is referred to in
	 * a function.
	 */
	public static final StreamVariable Y = new StreamVariable(1);
	
	/**
	 * A variable standing for the third input stream
	 * (i.e. argument number 2). It is recommended to reuse this
	 * instance everywhere the first argument is referred to in
	 * a function.
	 */
	public static final StreamVariable Z = new StreamVariable(2);
			
	/**
	 * The index of this variable
	 */
	protected int m_index;
	
	/**
	 * Creates a new trace placeholder
	 * @param index The index of the trace this placeholder represents
	 */
	public StreamVariable(int index)
	{
		super();
		m_index = index;
	}

	/**
	 * Creates a new trace placeholder, standing for the first
	 * input trace (i.e. index 0)
	 */
	public StreamVariable()
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
		if (o == null || !(o instanceof StreamVariable))
		{
			return false;
		}
		return m_index == ((StreamVariable) o).m_index;
	}

	@Override
	public void evaluate(Object[] inputs, Object[] outputs, Context context)
	{
		outputs[0] = inputs[m_index];
	}

	@Override
	public StreamVariable duplicate()
	{
		return this;
	}
	
	@Override
	public String toString()
	{
		return "$" + m_index;
	}
}
