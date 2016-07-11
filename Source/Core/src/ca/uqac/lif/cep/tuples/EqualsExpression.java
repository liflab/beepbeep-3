/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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

public class EqualsExpression extends BinaryExpression 
{
	public EqualsExpression(AttributeExpression left, AttributeExpression right)
	{
		super("=", left, right);
	}

	@Override
	public Object evaluate(Object t_left, Object t_right) 
	{
		if (t_left != null && t_right != null)
		{
			if (t_left instanceof Number && t_right instanceof Number)
			{
				return ((Number) t_left).floatValue() == ((Number) t_right).floatValue();
			}
			if (t_left instanceof String && t_right instanceof String)
			{
				return ((String) t_left).compareTo((String) t_right) == 0;
			}
			return t_left.equals(t_right);
		}
		return false;
	}
	
	public static void build(Stack<Object> stack) throws ConnectorException
	{
		stack.pop(); // )
		AttributeExpression exp_right = (AttributeExpression) stack.pop();
		stack.pop(); // (
		stack.pop(); // op
		stack.pop(); // )
		AttributeExpression exp_left = (AttributeExpression) stack.pop();
		stack.pop(); // (
		EqualsExpression op = new EqualsExpression(exp_left, exp_right);
		stack.push(op);
	}

}
