/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2026 Sylvain Hallé

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
package ca.uqac.lif.cep;

import ca.uqac.lif.petitpoucet.Part;

/**
 * A {@link Part} that designates a specific event in a stream.
 * @author Sylvain Hallé
 * @since 3.14
 */
public class EventAt implements Part
{
	/**
	 * The index of the event in the stream.
	 */
	protected final long m_position;
	
	/**
	 * Creates a new instance of the part.
	 * @param position The index of the event in the stream
	 */
	public EventAt(long position)
	{
		super();
		m_position = position;
	}
	
	/**
	 * Gets the index of the event in the stream.
	 * @return The index
	 */
	public long getPosition()
	{
		return m_position;
	}

	@Override
	public EventAt duplicate(boolean with_state)
	{
		return this;
	}
	
	@Override
	public int hashCode()
	{
		return (int) m_position;
	}
	
	@Override
	public boolean equals(Object o)
	{
		return o instanceof EventAt && ((EventAt) o).m_position == m_position;
	}
	
	@Override
	public String toString()
	{
		return "e[" + m_position + "]";
	}
}
