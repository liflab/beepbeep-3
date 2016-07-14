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
package ca.uqac.lif.cep.ltl;

import java.util.Queue;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.ltl.Troolean.Value;

/**
 * Troolean implementation of the LTL <b>X</b> operator
 * @author Sylvain Hallé
 */
public class After extends SingleProcessor 
{
	/**
	 * The number of events received so far
	 */
	private int m_eventCount = 0;
	
	/**
	 * The value to return (so far)
	 */
	private Value m_valueToReturn = Value.INCONCLUSIVE;
	
	public After()
	{
		super(1, 1);
	}

	@Override
	protected Queue<Object[]> compute(Object[] input) 
	{
		if (m_eventCount == 0)
		{
			m_eventCount = 1;
			return wrapObject(Value.INCONCLUSIVE);
		}
		else if (m_eventCount == 1)
		{
			m_eventCount = 2;
			m_valueToReturn = Troolean.trooleanValue(input[0]);
		}
		return wrapObject(m_valueToReturn);
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_valueToReturn = Value.INCONCLUSIVE;
		m_eventCount = 0;
	}

	@Override
	public Processor clone() 
	{
		return new After();
	}

}
