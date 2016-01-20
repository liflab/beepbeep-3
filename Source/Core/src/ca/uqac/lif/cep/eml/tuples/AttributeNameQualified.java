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
package ca.uqac.lif.cep.eml.tuples;

import java.util.Stack;

import ca.uqac.lif.util.CacheMap;

public class AttributeNameQualified extends AttributeName
{
	protected final String m_traceName;
	
	protected final String m_attributeName;
	
	private int m_attributeIndex = -1;
	
	private int m_tupleIndex = -1;
	
	public AttributeNameQualified(String trace, String attribute)
	{
		super();
		m_traceName = trace;
		m_attributeName = attribute;
	}
	
	public AttributeNameQualified(String attribute)
	{
		super();
		m_traceName = null;
		m_attributeName = attribute;
	}

	public static void build(Stack<Object> stack)
	{
		String att_name = EmlString.parseString(stack.pop());
		stack.pop(); // dot
		String trace_name = EmlString.parseString(stack.pop());
		AttributeNameQualified anq = new AttributeNameQualified(trace_name, att_name);
		stack.push(anq);
	}

	@Override
	public Object evaluate(CacheMap<Object> inputs) 
	{
		Object relevant_tuple = null;
		if (m_traceName == null || m_traceName.isEmpty())
		{
			relevant_tuple = inputs.getValue(0);
		}
		else
		{
			if (m_tupleIndex < 0)
			{
				// Ask for the index and remember it
				m_tupleIndex = inputs.getIndexOf(m_traceName);
			}
			relevant_tuple = inputs.getValue(m_tupleIndex);
		}
		if (relevant_tuple instanceof NamedTupleFixed)
		{
			NamedTupleFixed ntf = (NamedTupleFixed) relevant_tuple;
			if (m_attributeIndex < 0)
			{
				// Ask for the index and remember it
				m_attributeIndex = ntf.getIndexOf(m_attributeName);
			}
			// Query tuple based on its index
			return ntf.getValue(m_attributeIndex);
		}
		else if (relevant_tuple instanceof NamedTupleMap)
		{
			NamedTupleMap nt = (NamedTupleMap) relevant_tuple;
			return nt.get(m_attributeName);
		}
		else
		{
			return Tuple.computeWrap(relevant_tuple, null);
		}
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append(m_traceName).append(".").append(m_attributeName);
		return out.toString();
	}
}
