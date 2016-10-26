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
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.util.CacheMap;

/**
 * Takes the output of multiple processors, and puts them into a named
 * map. The usefulness of this processor lies mostly in the ESQL language.
 * It makes it possible to write something like:
 * <pre>
 * APPLY (($A) + ($B)) WITH 
 *   (expression) AS $A, 
 *   (expression) AS $B
 * </pre>
 * <p>
 * <strong>Caveat emptor:</strong> The input processors of this processor must
 * be <em>distinct</em>. If the same processor instance occurs multiple
 * times, it will be pulled more than once. (Note though that this applies
 * to any n-ary processor.) 
 * @author Sylvain Hallé
 */
public class Collator extends SingleProcessor
{
	protected ProcessorExpressionList m_processorList;

	public Collator(ProcessorExpressionList list)
	{
		super(list.size(), 1);
		m_processorList = list;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		int size = m_processorList.size();
		String[] names = new String[size];
		Object[] values = new Object[size];
		int i = 0;
		for (ProcessorExpression pe : m_processorList)
		{
			names[i] = pe.m_name;
			values[i] = inputs[i];
			i++;
		}
		CacheMap<Object> map = new CacheMap<Object>(names, values);
		return wrapObject(map);
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException
	{
		ProcessorExpressionList pel = (ProcessorExpressionList) stack.pop();
		stack.pop(); // WITH
		Collator col = new Collator(pel);
		int i = 0;
		for (ProcessorExpression pe : pel)
		{
			Connector.connect(pe.m_processor, 0, col, i);
			i++;
		}
		stack.push(col);
	}

	@Override
	public Processor clone() 
	{
		return new Collator(m_processorList);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("WITH ").append(m_processorList);
		return out.toString();
	}

	public ProcessorExpressionList getProcessorList() 
	{
		return m_processorList;
	}
}
