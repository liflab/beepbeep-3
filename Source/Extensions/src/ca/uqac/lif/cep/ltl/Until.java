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
package ca.uqac.lif.cep.ltl;

import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;

public class Until extends BinaryProcessor 
{
	protected boolean m_left;
	
	protected boolean m_right;
	
	public Until()
	{
		super();
		m_left = true;
		m_right = false;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_left = true;
		m_right = false;
	}

	@Override
	protected Object compute(boolean left, boolean right)
	{
		if (m_right)
		{
			return true;
		}
		if (!m_left)
		{
			return false;
		}
		m_right = m_right || right;
		m_left = m_left && left;
		if (m_right)
		{
			return true;
		}
		if (!m_left)
		{
			return false;
		}
		return null;
	}
	
	public static void build(Stack<Object> stack) 
	{
		stack.pop(); // (
		Processor right = (Processor) stack.pop();
		stack.pop(); // )
		stack.pop(); // op
		stack.pop(); // (
		Processor left = (Processor) stack.pop();
		stack.pop(); // )
		Until op = new Until();
		Connector.connect(left, op, 0, 0);
		Connector.connect(right, op, 0, 1);
		stack.push(op);
	}

	@Override
	public Until clone()
	{
		return new Until();
	}
}
