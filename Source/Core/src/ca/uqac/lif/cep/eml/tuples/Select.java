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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

import ca.uqac.lif.cep.Connector;
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
		this(0);
	}
	
	public Select(int in_arity)
	{
		super(in_arity, 1);
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
		Select sel = new Select(pdl.size());
		sel.m_processors = pdl;
		// Connect each processor to the input
		int j = 0;
		for (ProcessorDefinition pd : pdl)
		{
			Connector.connect(pd.m_processor, sel, 0, j);
			j++;
		}
		sel.m_attributeList = al;
		stack.push(sel);
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		Map<String,Tuple> in = new HashMap<String,Tuple>();
		int i = 0;
		for (ProcessorDefinition pd : m_processors)
		{
			String alias = pd.getAlias();
			Object o = inputs.get(i);
			if (!(o instanceof Tuple))
			{
				// A SELECT should receive only tuples for input!
				return null; 
			}
			in.put(alias, (Tuple) o);
			i++;
		}
		Queue<Vector<Object>> out = new LinkedList<Vector<Object>>();
		Vector<Object> tuples = new Vector<Object>();
		Tuple t = computeCast(in);
		if (t != null)
		{
			tuples.add(t);
		}
		out.add(tuples);
		return out;
	}
	
	/**
	 * Performs the computation of the SELECT on a typecast vector of
	 * inputs
	 * @param inputs A map from trace aliases to the tuple coming from 
	 *   that trace
	 * @return The output tuple
	 */
	protected Tuple computeCast(Map<String,Tuple> inputs)
	{
		if (m_attributeList.size() == 1)
		{
			AttributeDefinition a_def = m_attributeList.getFirst();
			if (a_def instanceof AttributeDefinitionPlain)
			{
				// The select clause has a single attribute with no name:
				// the output is an unnamed tuple of size 1, i.e. a constant
				AttributeExpression a_exp = a_def.getExpression();
				return a_exp.evaluate(inputs);
			}
		}
		// In all other cases, we return a named tuple
		NamedTuple t_out = new NamedTuple();
		for (AttributeDefinition a_def : m_attributeList)
		{
			// For each attribute definition, evaluate and put its result
			// in the tuple with the given alias
			AttributeExpression a_exp = a_def.getExpression();
			EmlConstant a_result = a_exp.evaluate(inputs);
			String alias = a_def.getAlias();
			t_out.put(alias, a_result);
		}
		return t_out;
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
