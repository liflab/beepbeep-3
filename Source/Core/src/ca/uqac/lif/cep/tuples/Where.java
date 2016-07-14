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
package ca.uqac.lif.cep.tuples;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.util.CacheMap;

public class Where extends SingleProcessor
{
	protected final AttributeExpression m_filterExpression;
	
	private final CacheMap<Object> m_associations;

	public Where(AttributeExpression filter)
	{
		super(1, 1);
		m_filterExpression = filter;
		String[] dummy_keys = new String[1];
		m_associations = new CacheMap<Object>(dummy_keys);
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
		m_associations.putAt(0, in_tuple);
		Object result = m_filterExpression.evaluate(m_associations);
		if (EmlBoolean.parseBoolValue(result) == true)
		{
			Object[] v_o = new Object[1];
			v_o[0] =  in_tuple;
			out_q.add(v_o);
		}
		return out_q;
	}

	public static void build(Stack<Object> stack) throws ConnectorException 
	{
		AttributeExpression ae = (AttributeExpression) stack.pop();
		stack.pop(); // WHERE
		stack.pop(); // (
		Processor proc = (Processor) stack.pop();
		stack.pop(); // )
		Where w = new Where(ae);
		Connector.connect(proc, w);
		stack.push(w);
	}
	
	@Override
	public Where clone()
	{
		return new Where(m_filterExpression);
	}
}
