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

import java.util.ArrayDeque;
import java.util.Stack;

public class ProcessorDefinitionList extends ArrayDeque<ProcessorDefinition>
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 1L;
	
	public ProcessorDefinitionList()
	{
		super();
	}
	
	public static void build(Stack<Object> stack)
	{
		Object top = stack.peek();
		ProcessorDefinitionList new_pdl = new ProcessorDefinitionList();
		if (top instanceof ProcessorDefinitionList)
		{
			ProcessorDefinitionList pdl = (ProcessorDefinitionList) stack.pop();
			if (!stack.isEmpty())
			{
				stack.pop(); // ,
				ProcessorDefinition def = (ProcessorDefinition) stack.pop();
				new_pdl.add(def);
			}
			new_pdl.addAll(pdl);
		}
		else
		{
			ProcessorDefinition def = (ProcessorDefinition) stack.pop();
			new_pdl.add(def);
		}
		stack.push(new_pdl);
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
}
