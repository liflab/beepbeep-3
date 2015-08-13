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

import java.util.Map;
import java.util.Stack;

public abstract class BinaryExpression extends AttributeExpression
{
	protected AttributeExpression m_left;
	
	protected AttributeExpression m_right;
	
	protected String m_symbol;

	@Override
	public void build(Stack<Object> stack)
	{
		stack.pop(); // )
		AttributeExpression exp_right = (AttributeExpression) stack.pop();
		stack.pop(); // (
		do
		{
			m_symbol += (String) stack.pop(); // The symbol
		} while (((String) stack.peek()).compareTo(")") != 0);
		stack.pop(); // )
		AttributeExpression exp_left = (AttributeExpression) stack.pop();
		stack.pop(); // (
		m_left = exp_left;
		m_right = exp_right;
		stack.push(this);
	}
	
	@Override
	public EmlConstant evaluate(Map<String,Tuple> inputs)
	{
		Tuple t_left = m_left.evaluate(inputs);
		Tuple t_right = m_right.evaluate(inputs);
		return evaluate(t_left, t_right);
	}
	
	protected abstract EmlConstant evaluate(Object t_left, Object t_right);
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("(").append(m_left).append(") ").append(m_symbol).append(" (").append(m_right).append(")");
		return out.toString();
	}
}
