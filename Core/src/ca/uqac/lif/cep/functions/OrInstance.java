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
package ca.uqac.lif.cep.functions;

import java.util.ArrayDeque;

import ca.uqac.lif.cep.Connector.ConnectorException;

/**
 * Instance of the AND function. This class exists only so that we can
 * refer to it in an expression of the form:
 * <pre>
 * COMBINE (something) WITH DISJUNCTION
 * </pre>
 * 
 * @author Sylvain Hallé
 */
class OrInstance extends Or
{
	public static final transient OrInstance instance = new OrInstance();

	OrInstance()
	{
		super();
	}

	public static void build(ArrayDeque<Object> stack) throws ConnectorException
	{
		stack.pop(); // the name
		stack.push(instance);
	}
}
