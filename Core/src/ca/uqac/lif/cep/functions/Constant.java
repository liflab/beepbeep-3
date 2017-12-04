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
 * Representation of a unary constant
 * @author Sylvain Hallé
 */
public class Constant extends Function
{
	/**
	 * A constant representing the number zero
	 */
	public static final Constant ZERO = new Constant(0);
	
	/**
	 * A constant representing the number one
	 */
	public static final Constant ONE = new Constant(1);
	
	/**
	 * The value to return by this constant
	 */
	private final Object m_value;

	/**
	 * Creates a new constant
	 * @param value The value associated to this constant
	 */
	public Constant(Object value)
	{
		super();
		m_value = value;
	}

	@Override
	public void evaluate(Object[] inputs, Object[] outputs, Context context)
	{
		outputs[0] = m_value;
	}

	@Override
	public void evaluate(Object[] inputs, Object[] outputs)
	{
		evaluate(inputs, outputs, null);
	}

	@Override
	public int getInputArity()
	{
		return 0;
	}

	@Override
	public int getOutputArity()
	{
		return 1;
	}

	@Override
	public void reset()
	{
		// Nothing to do
	}

	@Override
	public Constant duplicate()
	{
		return new Constant(m_value);
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index)
	{
		// Nothing to do
		return;
	}

	@Override
	public Class<?> getOutputTypeFor(int index)
	{
		return m_value.getClass();
	}

	@Override
	public String toString()
	{
		if (m_value == null)
		{
			return "null";
		}
		return m_value.toString();
	}

	/**
	 * Gets the actual object that this constant processor returns
	 * @return The value
	 */
	public Object getValue()
	{
		return m_value;
	}
}
