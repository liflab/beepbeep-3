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
import java.util.Map;
import java.util.ArrayDeque;

public class UserDefinitionInstance
{
	protected UserDefinition m_definition;

	public UserDefinitionInstance(UserDefinition definition)
	{
		super();
		m_definition = definition;
	}

	public void build(ArrayDeque<Object> stack)
	{
		// Pull stuff from the stack based on the parsing pattern
		Map<String,Object> variable_definitions = new HashMap<String,Object>();
		String[] pattern_parts = m_definition.m_pattern.split(" ");
		for (int i = pattern_parts.length - 1; i >= 0; i--)
		{
			// Read from the end
			String part = pattern_parts[i];
			if (part.startsWith("@"))
			{
				// This is a variable; pop the object and associate it with
				// the variable name
				Object o = stack.pop();
				variable_definitions.put(part, o);
			}
			else
			{
				// This is not a variable; eat the corresponding
				// symbol from the stack and do nothing with it
				stack.pop();
			}
		}
		// Now that we have the variable associations, parse the definition
		Object o = m_definition.parseDefinition(variable_definitions);
		stack.push(o);
	}

	@Override
	public String toString()
	{
		return m_definition.toString();
	}

}
