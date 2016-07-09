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

import ca.uqac.lif.cep.util.CacheMap;

public abstract class UnaryExpression extends AttributeExpression
{
	protected final AttributeExpression m_left;
	
	protected final String m_symbol;
	
	public UnaryExpression(String symbol, AttributeExpression exp)
	{
		super();
		m_left = exp;
		m_symbol = symbol;
	}
	
	@Override
	public Object evaluate(CacheMap<Object> inputs)
	{
		Object t_left = m_left.evaluate(inputs);
		return evaluate(t_left);
	}
	
	protected abstract Object evaluate(Object t_left);
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append(m_symbol).append("(").append(m_left).append(")");
		return out.toString();
	}
}
