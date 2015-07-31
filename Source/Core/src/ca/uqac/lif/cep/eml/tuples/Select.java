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

import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

import ca.uqac.lif.cep.SingleProcessor;

public class Select extends SingleProcessor
{
	/**
	 * The list of processors appearing in the "FROM" part
	 * of the statement
	 */
	protected ProcessorDefinitionList m_processors;
	
	/**
	 * The list of attribute expressions appearing in the "SELECT"
	 * part of the statement
	 */
	protected AttributeList m_attributeList;
	
	public Select()
	{
		super();
		m_processors = null;
		m_attributeList = null;
	}

	@Override
	public void build(Stack<Object> stack)
	{
		ProcessorDefinitionList pdl = (ProcessorDefinitionList) stack.pop(); 
		stack.pop(); // FROM
		AttributeList al = (AttributeList) stack.pop();
		stack.pop(); // SELECT
		m_processors = pdl;
		m_attributeList = al;
		stack.push(this);
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("SELECT ").append(m_attributeList)
			.append(" FROM ").append(m_processors);
		return out.toString();
	}
}
