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

import ca.uqac.lif.cep.Buildable;

public abstract class AttributeDefinition implements Buildable
{
	protected AttributeExpression m_expression;
	
	protected String m_aliasName;
	
	public AttributeDefinition()
	{
		super();
		m_expression = null;
		m_aliasName = "";
	}
	
	public String getAlias()
	{
		return m_aliasName;
	}
	
	public AttributeExpression getExpression()
	{
		return m_expression;
	}
	
	@Override
	public AttributeDefinition newInstance()
	{
		AttributeDefinition out = null;
		Class<?> c = this.getClass();
		try {
			out = (AttributeDefinition) c.newInstance();
		} catch (InstantiationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return out;
	}
}
