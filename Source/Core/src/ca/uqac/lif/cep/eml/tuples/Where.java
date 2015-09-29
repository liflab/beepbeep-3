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
package ca.uqac.lif.cep.eml.tuples;

import java.util.HashMap;
import java.util.ArrayDeque;
import java.util.Map;
import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;

public class Where extends SingleProcessor
{
	protected AttributeExpression m_filterExpression;

	public Where()
	{
		super(1, 1);
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Queue<Object[]> out_q = new ArrayDeque<Object[]>();
		Object first_elem = inputs[0];
		if (!(first_elem instanceof Tuple))
		{
			// The WHERE processor should receive only tuples
			return null;
		}
		Tuple in_tuple = (Tuple) first_elem;
		Map<String,Tuple> associations = new HashMap<String,Tuple>();
		associations.put("", in_tuple);
		EmlConstant result = m_filterExpression.evaluate(associations);
		if (result instanceof EmlBoolean)
		{
			EmlBoolean b = (EmlBoolean) result;
			if (b.boolValue())
			{
				Object[] v_o = new Object[1];
				v_o[0] =  in_tuple;
				out_q.add(v_o);
			}
		}
		return out_q;
	}

	@Override
	public void build(Stack<Object> stack) 
	{
		AttributeExpression ae = (AttributeExpression) stack.pop();
		stack.pop(); // WHERE
		stack.pop(); // (
		Processor proc = (Processor) stack.pop();
		stack.pop(); // )
		m_filterExpression = ae;
		Connector.connect(proc, this);
		stack.push(this);
	}
}
