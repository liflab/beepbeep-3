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

public abstract class AttributeDefinition
{
	protected final AttributeExpression m_expression;
	
	protected final String m_aliasName;
	
	public AttributeDefinition(AttributeExpression exp, String alias)
	{
		super();
		m_expression = exp;
		m_aliasName = alias;
	}
	
	public String getAlias()
	{
		return m_aliasName;
	}
	
	public AttributeExpression getExpression()
	{
		return m_expression;
	}
}
