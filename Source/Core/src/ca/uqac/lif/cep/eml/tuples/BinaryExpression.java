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
package ca.uqac.lif.cep.eml.tuples;

import ca.uqac.lif.util.CacheMap;

public abstract class BinaryExpression extends AttributeExpression
{
	protected final AttributeExpression m_left;
	
	protected final AttributeExpression m_right;
	
	protected final String m_symbol;
	
	BinaryExpression(String symbol, AttributeExpression left, AttributeExpression right)
	{
		super();
		m_left = left;
		m_right = right;
		m_symbol = symbol;
	}
	
	@Override
	public Object evaluate(CacheMap<Object> inputs)
	{
		Object t_left = m_left.evaluate(inputs);
		Object t_right = m_right.evaluate(inputs);
		return evaluate(t_left, t_right);
	}
	
	protected abstract Object evaluate(Object t_left, Object t_right);
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("(").append(m_left).append(") ").append(m_symbol).append(" (").append(m_right).append(")");
		return out.toString();
	}
}
