/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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

import ca.uqac.lif.cep.ProcessorException;

/**
 * Faucet that creates an output event based on the last event
 * received
 * @author Sylvain Hallé
 */
public class LastFaucet extends Faucet
{
	/**
	 * The last event received
	 */
	protected Object m_last;

	@Override
	public void onPush(Object e)
	{
		m_last = e;
	}

	@Override
	public final boolean onPull(Queue<Object[]> queue) throws ProcessorException
	{
		queue.add(new Object[]{onPull(m_last)});
		return true;
	}
	
	/**
	 * Create an output event from the last event received
	 * @param o The last event received
	 * @return An output event
	 * @throws ProcessorException 
	 */
	public Object onPull(Object o) throws ProcessorException
	{
		return o;
	}

	@Override
	public LastFaucet clone()
	{
		return new LastFaucet();
	}

}