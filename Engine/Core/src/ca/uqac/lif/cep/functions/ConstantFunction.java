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
public class ConstantFunction extends Function
{
	protected Object m_value;
	
	public ConstantFunction(Object value)
	{
		m_value = value;
	}
	
	@Override
	public Object[] evaluate(Object[] inputs, Context context)
	{
		Object[] out = new Object[1];
		out[0] = m_value;
		return out;
	}

	@Override
	public Object[] evaluate(Object[] inputs) 
	{
		return evaluate(inputs, null);
	}

	@Override
	public int getInputArity() {
		// TODO Auto-generated method stub
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
	public ConstantFunction clone() 
	{
		return new ConstantFunction(m_value);
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
}
