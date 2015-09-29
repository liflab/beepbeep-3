/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep;

import java.util.Queue;
import java.util.Stack;

public class Prefix extends Delay
{
	public Prefix()
	{
		super();
	}
	
	public Prefix(int k)
	{
		super(k);
	}
	
	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		m_eventsReceived++;
		if (m_eventsReceived < m_delay)
		{
			return wrapVector(inputs);
		}
		return null;
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		Processor p = (Processor) stack.pop();
		stack.pop(); // OF
		Number interval = (Number) stack.pop();
		Prefix out = new Prefix(interval.intValue());
		Connector.connect(p, out);
		stack.push(out);
	}
}
