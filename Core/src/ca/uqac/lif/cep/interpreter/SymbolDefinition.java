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

import java.util.ArrayDeque;

import ca.uqac.lif.cep.Connector.ConnectorException;

public class SymbolDefinition
{
	/**
	 * The non terminal symbol this definition stands for
	 */
	protected final String m_symbolName;

	/**
	 * The variable name of this definition
	 */
	protected final String m_variableName;

	public SymbolDefinition(String symbol_name, String variable_name)
	{
		super();
		// Hack; we assume all non-terminals are lowercase
		m_symbolName = symbol_name.toLowerCase();
		m_variableName = variable_name;
	}

	public String getName()
	{
		return m_variableName;
	}

	public String getSymbol()
	{
		return m_symbolName;
	}

	public static void build(ArrayDeque<Object> stack) throws ConnectorException
	{
		String symbol_name = (String) stack.pop();
		stack.pop(); // A
		stack.pop(); // IS
		String variable_name = (String) stack.pop();
		SymbolDefinition sd = new SymbolDefinition(symbol_name, variable_name);
		stack.push(sd);
	}

}
