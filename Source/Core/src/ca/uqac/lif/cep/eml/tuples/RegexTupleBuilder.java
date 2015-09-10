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

import java.util.ArrayList;
import java.util.Queue;
import java.util.Stack;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ca.uqac.lif.cep.Buildable;
import ca.uqac.lif.cep.Connector;
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
	
	public RegexTupleBuilder()
	{
		super();
		m_pattern = null;
		m_attributeNames = new RegexAttributeNameList();
	}
	
	/**
	 * Sets the pattern to look for
	 * @param regex The pattern. This can be any regular expression.
	 */
	public void setPattern(String regex)
	{
		m_pattern = Pattern.compile(regex);
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs) 
	{
		Vector<Object> out_vector = new Vector<Object>();
		int num_names = m_attributeNames.size();
		String s = (String) inputs.firstElement();
		Matcher mat = m_pattern.matcher(s);
		if (!mat.find())
		{
			// The pattern was not found: don't output anything
			return null;
		}
		NamedTuple tuple = new NamedTuple();
		int group_count = mat.groupCount();
		for (int i = 1; i < group_count; i++) // i=0 is the entire pattern
		{
			String group = mat.group(i);
			String name = new Integer(i).toString();
			if (i < num_names)
			{
				name = m_attributeNames.get(i - 1).m_attributeName;
			}
			tuple.put(name, new EmlString(group));
		}
		out_vector.add(tuple);
		return wrapVector(out_vector);
	}

	@Override
	public void build(Stack<Object> stack)
	{
		stack.pop(); // )
		Processor p = (Processor) stack.pop();
		stack.pop(); // (
		stack.pop(); // IN		
		m_attributeNames = (RegexAttributeNameList) stack.pop();
		stack.pop(); // NAMES
		stack.pop(); // WITH
		String regex = stack.pop().toString();
		setPattern(regex);
		stack.pop(); // REGEX
		Connector.connect(p, this);
		stack.push(this);
	}
	
	public static class RegexAttributeNameList extends ArrayList<AttributeNamePlain> implements Buildable
	{
		/**
		 * Dummy UID
		 */
		private static final long serialVersionUID = 1L;
		
		public RegexAttributeNameList()
		{
			super();
		}

		@Override
		public void build(Stack<Object> stack)
		{
			Object top = stack.peek();
			if (top instanceof RegexAttributeNameList)
			{
				RegexAttributeNameList al = (RegexAttributeNameList) stack.pop();
				if (!stack.isEmpty())
				{
					stack.pop(); // ,
					AttributeNamePlain def = (AttributeNamePlain) stack.pop();
					add(def);
				}
				addAll(al);
			}
			else
			{
				AttributeNamePlain def = (AttributeNamePlain) stack.pop();
				add(def);
			}
			stack.push(this);
		}

		@Override
		public Buildable newInstance() 
		{
			return new RegexAttributeNameList();
		}
		
	}

}
