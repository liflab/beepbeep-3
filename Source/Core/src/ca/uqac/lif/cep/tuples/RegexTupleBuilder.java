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

import java.util.ArrayList;
import java.util.Queue;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * Builds a tuple out of parts of text. The parts of text to create
 * the tuple from are specified by a regular expression.
 * <p>
 * More precisely, each element of the tuple corresponds to a <em>capture
 * block</em> of the regex: the first capture block will correspond
 * to the tuple's first element, the second to the second, and so on.
 * By default, the name of each element is a number, with the first
 * capture block starting at 0. Optionally, these elements can be
 * renamed to arbitrary character strings.
 * 
 */
public class RegexTupleBuilder extends SingleProcessor 
{
	/**
	 * The regex pattern to look for
	 */
	protected Pattern m_pattern;
	
	/**
	 * The name given to each capture block in the output tuples 
	 */
	protected RegexAttributeNameList m_attributeNames;
	
	RegexTupleBuilder()
	{
		super(1, 1);
	}
	
	/**
	 * Constructs a tuple builder.
	 * @param regex The pattern. This can be any regular expression.
	 * @param attributes The attribute names to give each capture
	 *   block
	 */
	public RegexTupleBuilder(String regex, RegexAttributeNameList attributes)
	{
		super(1, 1);
		m_pattern = Pattern.compile(regex);
		m_attributeNames = attributes;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs) 
	{
		Object[] out_vector = new Object[1];
		int num_names = m_attributeNames.size();
		String s = (String) inputs[0];
		Matcher mat = m_pattern.matcher(s);
		if (!mat.find())
		{
			// The pattern was not found: don't output anything
			return null;
		}
		NamedTupleMap tuple = new NamedTupleMap();
		int group_count = mat.groupCount();
		for (int i = 1; i < group_count; i++) // i=0 is the entire pattern
		{
			String group = mat.group(i);
			String name = new Integer(i).toString();
			if (i < num_names)
			{
				name = m_attributeNames.get(i - 1).m_attributeName;
			}
			tuple.put(name, group);
		}
		out_vector[0] = tuple;
		return wrapVector(out_vector);
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		stack.pop(); // )
		Processor p = (Processor) stack.pop();
		stack.pop(); // (
		stack.pop(); // IN		
		RegexAttributeNameList attributes = (RegexAttributeNameList) stack.pop();
		stack.pop(); // NAMES
		stack.pop(); // WITH
		String regex = stack.pop().toString();
		stack.pop(); // REGEX
		RegexTupleBuilder rtp = new RegexTupleBuilder(regex, attributes);
		Connector.connect(p, rtp);
		stack.push(rtp);
	}
	
	public static class RegexAttributeNameList extends ArrayList<AttributeNamePlain>
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;
		
		public RegexAttributeNameList()
		{
			super();
		}

		public static void build(Stack<Object> stack) throws ConnectorException
		{
			Object top = stack.peek();
			RegexAttributeNameList ranl = new RegexAttributeNameList();
			if (top instanceof RegexAttributeNameList)
			{
				RegexAttributeNameList al = (RegexAttributeNameList) stack.pop();
				if (!stack.isEmpty())
				{
					stack.pop(); // ,
					AttributeNamePlain def = (AttributeNamePlain) stack.pop();
					ranl.add(def);
				}
				ranl.addAll(al);
			}
			else
			{
				AttributeNamePlain def = (AttributeNamePlain) stack.pop();
				ranl.add(def);
			}
			stack.push(ranl);
		}		
	}
	
	@Override
	public RegexTupleBuilder clone()
	{
		RegexTupleBuilder out = new RegexTupleBuilder();
		out.m_pattern = m_pattern;
		out.m_attributeNames = m_attributeNames;
		return out;
	}

}
