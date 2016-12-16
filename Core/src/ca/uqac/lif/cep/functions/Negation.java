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
 * Implementation of the logical negation
 * 
 * @author Sylvain Hallé
 */
public class Negation extends UnaryFunction<Boolean,Boolean>
{
	public static final transient Negation instance = new Negation();

	Negation()
	{
		super(Boolean.class, Boolean.class);
	}

	@Override
	public Boolean getValue(Boolean x)
	{
		return !x.booleanValue();
	}

	@Override
	public String toString()
	{
		return "¬";
	}

	public static void build(ArrayDeque<Object> stack) throws ConnectorException
	{
		Object o;
		Function f;
		o = stack.pop(); // ( ?
		if (o instanceof String)
		{
			f = (Function) stack.pop();
			stack.pop(); // )
		}
		else
		{
			f = (Function) o;
		}
		stack.pop(); // symbol
		FunctionTree ft = new FunctionTree(instance, f);
		stack.push(ft);
	}
}
