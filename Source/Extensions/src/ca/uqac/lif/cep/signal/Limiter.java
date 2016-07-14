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
package ca.uqac.lif.cep.signal;

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.tuples.EmlNumber;

/**
 * Outputs at most one non-zero event in an interval of width <i>n</i>.
 * @author Sylvain Hallé
 *
 */
public class Limiter extends SingleProcessor
{
	protected final int m_limit;
	
	protected int m_counter;
	
	public Limiter()
	{
		this(5);
	}
	
	public Limiter(int width)
	{
		super(1, 1);
		m_limit = width;
		m_counter = 0;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		m_counter--;
		float value = EmlNumber.parseFloat(inputs[0]);
		if (m_counter > 0 || value == 0)
		{
			// Ignore this event
			return wrapObject(0);
		}
		m_counter = m_limit;
		
		return wrapObject(value);
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		// TODO Auto-generated method stub
	}
	
	@Override
	public Limiter clone()
	{
		return new Limiter(m_limit);
	}

}
