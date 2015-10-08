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
package ca.uqac.lif.cep.signal;

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.eml.tuples.EmlNumber;

public class Threshold extends SingleProcessor
{
	protected float m_threshold;
	
	public Threshold()
	{
		this(0);
	}
	
	public Threshold(float threshold)
	{
		super(1, 1);
		m_threshold = threshold;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		float value = EmlNumber.parseFloat(inputs[0]);
		if (value > m_threshold)
		{
			return wrapObject(new EmlNumber(value));
		}
		return wrapObject(new EmlNumber(0));
	}

	@Override
	public void build(Stack<Object> stack)
	{
		m_threshold = EmlNumber.parseFloat(stack.pop());
		stack.pop(); // THRESHOLD
		stack.pop(); // (
		Processor p = (Processor) stack.pop();
		stack.pop(); // )
		Connector.connect(p,  this);
		stack.push(this);
		
	}

}
