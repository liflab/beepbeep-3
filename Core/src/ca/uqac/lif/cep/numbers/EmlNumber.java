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
package ca.uqac.lif.cep.numbers;

import java.util.ArrayDeque;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.functions.Constant;

/**
 * Used to create a constant out of a number
 * @author Sylvain Hallé
 *
 */
public class EmlNumber extends Constant
{
	public EmlNumber()
	{
		super(null);
	}

	public EmlNumber(Object o)
	{
		super(o);
	}

	public static void build(ArrayDeque<Object> stack) throws ConnectorException
	{
		Object o = stack.pop();
		if (o instanceof Number)
		{
			stack.push(new EmlNumber(o));
		}
		else if (o instanceof String)
		{
			float f = Float.parseFloat((String) o);
			stack.push(new EmlNumber(f));
		}
		else
		{
			// Put back on the stack
			stack.push(o);
		}
	}

	public int intValue()
	{
		return ((Number) getValue()).intValue();
	}
}
