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
package ca.uqac.lif.cep.interpreter;

import java.util.HashMap;
import java.util.Stack;

import ca.uqac.lif.cep.Connector.ConnectorException;

public class SymbolDefinitionList extends HashMap<String, String>
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 1L;

	public SymbolDefinitionList()
	{
		super();
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		Object top = stack.peek();
		SymbolDefinitionList new_sdl = new SymbolDefinitionList();
		if (top instanceof SymbolDefinitionList)
		{
			SymbolDefinitionList sdl = (SymbolDefinitionList) stack.pop();
			if (!stack.isEmpty())
			{
				stack.pop(); // ,
				SymbolDefinition def = (SymbolDefinition) stack.pop();
				new_sdl.put(def.getName(), def.getSymbol());
			}
			new_sdl.putAll(sdl);
		}
		else
		{
			SymbolDefinition def = (SymbolDefinition) stack.pop();
			new_sdl.put(def.getName(), def.getSymbol());
		}
		stack.push(new_sdl);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		boolean first = true;
		for (String def : this.keySet())
		{
			if (!first)
			{
				out.append(", ");
			}
			first = false;
			out.append(def).append(" IS A ").append(get(def));
		}
		return out.toString();
	}

}
