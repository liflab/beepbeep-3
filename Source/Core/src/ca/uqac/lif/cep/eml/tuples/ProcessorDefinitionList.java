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

import java.util.LinkedList;
import java.util.Stack;

import ca.uqac.lif.cep.Buildable;

public class ProcessorDefinitionList extends LinkedList<ProcessorDefinition> implements Buildable
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 1L;
	
	public ProcessorDefinitionList()
	{
		super();
	}

	@Override
	public void build(Stack<Object> stack)
	{
		Object top = stack.peek();
		if (top instanceof ProcessorDefinitionList)
		{
			ProcessorDefinitionList pdl = (ProcessorDefinitionList) stack.pop();
			if (!stack.isEmpty())
			{
				stack.pop(); // ,
				ProcessorDefinition def = (ProcessorDefinition) stack.pop();
				add(def);
			}
			addAll(pdl);
		}
		else
		{
			ProcessorDefinition def = (ProcessorDefinition) stack.pop();
			add(def);
		}
		stack.push(this);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		boolean first = true;
		for (ProcessorDefinition def : this)
		{
			if (!first)
			{
				out.append(", ");
			}
			first = false;
			out.append(def);
		}
		return out.toString();
	}
	
	@Override
	public ProcessorDefinitionList newInstance()
	{
		return new ProcessorDefinitionList();
	}
}
