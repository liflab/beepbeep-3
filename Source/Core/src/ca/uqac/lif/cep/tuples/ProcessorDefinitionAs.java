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

import java.util.Stack;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;

public class ProcessorDefinitionAs extends ProcessorDefinition
{	
	public ProcessorDefinitionAs()
	{
		super();
	}
	
	public ProcessorDefinitionAs(String name, Processor p)
	{
		this();
		m_processorName = name;
		m_processor = p;
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		String name = EmlString.parseString(stack.pop());
		Processor proc = null;
		stack.pop(); // AS
		Object o = stack.peek();
		if (o instanceof String && ((String)o).compareTo(")") == 0)
		{
			// We are in the case where there are
			// parentheses around the processor
			stack.pop(); // )
			proc = Processor.liftProcessor(stack.pop());
			stack.pop(); // (
		}
		else
		{
			proc = Processor.liftProcessor(stack.pop());
		}
		ProcessorDefinitionAs pda = new ProcessorDefinitionAs(name, proc);
		stack.push(pda);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append(m_processor).append(" AS ").append(m_processorName);
		return out.toString();
	}
}
