/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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
package ca.uqac.lif.cep.eml.tuples;

public final class FixedTupleBuilder
{
	private final String[] m_names;
	
	public FixedTupleBuilder(String[] names)
	{
		super();
		m_names = names;
	}
	
	public final NamedTupleFixed createTuple(Object[] values)
	{
		return new NamedTupleFixed(m_names, values);
	}
	
	public final NamedTupleFixed createTupleFromString(String[] values)
	{
		Object[] eml_values = new Object[values.length];
		for (int i = 0; i < values.length; i++)
		{
			eml_values[i] = EmlConstant.createConstantFromString(values[i]);
		}
		return new NamedTupleFixed(m_names, eml_values);
	}	
}
