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
package ca.uqac.lif.cep.jdbc;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.tuples.EmlNumber;
import ca.uqac.lif.cep.tuples.NamedTuple;

public class BeepBeepResultSet extends EmptyResultSet
{
	/**
	 * The {@link Pullable} this result set will pull its results from
	 */
	protected final Pullable m_pullable;
	
	/**
	 * The last tuple return by a call to {@link Pullable#pullHard()}
	 */
	protected NamedTuple m_lastTuple;
	
	/**
	 * Constructor of a result set
	 * @param p The pullable this result set will pull its results from
	 */
	BeepBeepResultSet(Pullable p)
	{
		super();
		m_pullable = p;
		m_lastTuple = null;
	}
	
	@Override
	public boolean next()
	{
		boolean status = m_pullable.hasNextHard() != Pullable.NextStatus.NO;
		if (status)
		{
			m_lastTuple = (NamedTuple) m_pullable.pullHard();
		}
		return status;
	}
	
	@Override
	public String getString(String attribute)
	{
		if (m_lastTuple == null || !m_lastTuple.containsKey(attribute))
		{
			return null;
		}
		return m_lastTuple.get(attribute).toString();
	}
	
	@Override
	public int getInt(String attribute)
	{
		return (int) getFloat(attribute);
	}
	
	@Override
	public float getFloat(String attribute)
	{
		if (m_lastTuple == null || !m_lastTuple.containsKey(attribute))
		{
			return 0;
		}
		Object o = m_lastTuple.get(attribute);
		return EmlNumber.parseFloat(o);
	}

	@Override
	public double getDouble(String attribute)
	{
		return (double) getFloat(attribute);
	}
}
