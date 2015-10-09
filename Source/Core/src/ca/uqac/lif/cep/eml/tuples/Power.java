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

import java.util.Stack;

public class Power extends BinaryExpression
{
	public Power(String symbol, AttributeExpression left, AttributeExpression right)
	{
		super(symbol, left, right);
	}
	
	@Override
	public EmlConstant evaluate(Object t_left, Object t_right)
	{
		float n_left = EmlNumber.parseFloat(t_left);
		float n_right = EmlNumber.parseFloat(t_right);
		return new EmlNumber(Math.pow(n_left, n_right));
	}
	
	public static void build(Stack<Object> stack)
	{
		String symbol = (String) stack.pop(); // RD, TH, ND, etc.
		stack.pop(); // )
		AttributeExpression exp_right = (AttributeExpression) stack.pop();
		stack.pop(); // (
		stack.pop(); // THE
		stack.pop(); // TO
		stack.pop(); // )
		AttributeExpression exp_left = (AttributeExpression) stack.pop();
		stack.pop(); // (
		Power p = new Power(symbol, exp_left, exp_right);
		stack.push(p);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("(").append(m_left).append(") TO THE (").append(m_right).append(") ").append(m_symbol);
		return out.toString();
	}

}
