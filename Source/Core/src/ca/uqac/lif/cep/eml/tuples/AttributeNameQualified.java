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

import java.util.Map;
import java.util.Stack;

public class AttributeNameQualified extends AttributeName
{
	protected String m_traceName;
	
	protected String m_attributeName;
	
	public AttributeNameQualified()
	{
		this("", "");
	}
	
	public AttributeNameQualified(String trace, String attribute)
	{
		super();
		m_traceName = trace;
		m_attributeName = attribute;
	}

	@Override
	public void build(Stack<Object> stack)
	{
		EmlString att_name = (EmlString) stack.pop();
		stack.pop(); // dot
		EmlString trace_name = (EmlString) stack.pop();
		m_traceName = trace_name.stringValue();
		m_attributeName = att_name.stringValue();
		stack.push(this);
	}

	@Override
	public EmlConstant evaluate(Map<String,Tuple> inputs) 
	{
		Tuple relevant_tuple = null;
		if (m_traceName == null || m_traceName.isEmpty())
		{
			relevant_tuple = inputs.get("");
		}
		else
		{
			relevant_tuple = inputs.get(m_traceName);
		}
		if (relevant_tuple instanceof NamedTuple)
		{
			NamedTuple nt = (NamedTuple) relevant_tuple;
			return nt.get(m_attributeName);
		}
		else if (relevant_tuple instanceof EmlConstant)
		{
			return (EmlConstant) relevant_tuple;
		}
		return null;
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append(m_traceName).append(".").append(m_attributeName);
		return out.toString();
	}
}
