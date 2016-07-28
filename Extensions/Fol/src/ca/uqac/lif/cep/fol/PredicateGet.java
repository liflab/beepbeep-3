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
package ca.uqac.lif.cep.fol;

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Extracts the value at a specific position in the predicate tuple.
 */
public class PredicateGet extends UnaryFunction<PredicateTuple,Object>
{
	/**
	 * The position to extract from each tuple
	 */
	protected int m_position;

	/**
	 * Creates an instance of the function
	 * @param position The position to extract in a tuple. If
	 * <code>position</code> = 0, the name of the predicate tuple
	 * will be returned. Otherwise, the value at index <code>position</code>-1
	 * in the arguments will be returned. The value <code>null</code> will
	 * be returned if the index is out of bounds with respect to the
	 * tuple being given.
	 */
	public PredicateGet(int position)
	{
		super(PredicateTuple.class, Object.class);
		m_position = position;
	}

	@Override
	public Object getValue(PredicateTuple x) 
	{
		if (m_position == 0)
		{
			return x.m_name;
		}
		return x.getArgument(m_position - 1);
	}

	@Override
	public PredicateGet clone()
	{
		return new PredicateGet(m_position);
	}
}