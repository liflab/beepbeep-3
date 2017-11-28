/*
    Log trace triaging and etc.
    Copyright (C) 2016 Sylvain Hallé

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
package ca.uqac.lif.cep.sets;

import java.util.Set;

import ca.uqac.lif.cep.functions.Function;

/**
 * Converts <i>n</i> input events into a list of size <i>n</i>
 * @author Sylvain Hallé
 */
public class ToList extends Function
{
	/**
	 * 
	 */
	private static final long serialVersionUID = -522369408913758577L;
	protected Class<?>[] m_types;
	
	public ToList(Class<?> ... types)
	{
		super();
		m_types = types;
	}
	@Override
	public void evaluate(Object[] inputs, Object[] outputs) 
	{
		MathList<Object> list = new MathList<Object>();
		for (Object o : inputs)
		{
			list.add(o);
		}
		outputs[0] = list;
	}

	@Override
	public int getInputArity()
	{
		return m_types.length;
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
	public ToList duplicate() 
	{
		return new ToList(m_types);
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index) 
	{
		classes.add(m_types[index]);
	}

	@Override
	public Class<?> getOutputTypeFor(int index) 
	{
		return MathList.class;
	}
}
