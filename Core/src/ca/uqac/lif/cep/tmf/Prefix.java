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
package ca.uqac.lif.cep.tmf;

import java.util.Queue;

/**
 * Returns the first <i>n</i> input events and discards the following ones.
 * 
 * @author Sylvain Hallé
 */
@SuppressWarnings("squid:S2160")
public class Prefix extends Trim
{
	public Prefix(int k)
	{
		super(k);
	}

	@Override
	@SuppressWarnings("squid:S1168")
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		m_eventsReceived++;
		if (m_eventsReceived <= getDelay())
		{
			outputs.add(inputs);
			return true;
		}
		return false;
	}

	@Override
	public void reset()
	{
		super.reset();
		m_eventsReceived = 0;
	}
}
