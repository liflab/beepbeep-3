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

import java.util.Set;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.functions.SimpleFunction;
import ca.uqac.lif.cep.util.CacheMap;

public class SelectFunction extends SimpleFunction
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
	
	protected FixedTupleBuilder m_builder;
	
	protected CacheMap<Object> m_aliases;
	
	protected int m_inputArity;
	
	public SelectFunction(int in_arity)
	{
		super();
		m_inputArity = in_arity;
		m_processors = null;
		m_attributeList = null;
		m_builder = null;
		m_aliases = null;
	}

	public SelectFunction(int in_arity, String ... attributes)
	{
		this(in_arity);
		setAttributeList(attributes);
	}
	
	public SelectFunction(int in_arity, AttributeExpression ... expressions)
	{
		this(in_arity);
		AttributeList al = new AttributeList();
		for (AttributeExpression aexp : expressions)
		{
			AttributeDefinition adef = new AttributeDefinitionPlain(aexp);
			al.add(adef);
		}
		m_attributeList = al;
	}
	
	public SelectFunction(int in_arity, AttributeDefinition... definitions)
	{
		this(in_arity);
		AttributeList al = new AttributeList();
		for (AttributeDefinition adef : definitions)
		{
			al.add(adef);
		}
		m_attributeList = al;
	}

	/**
	 * Convenience method to set the attributes of the selection
	 * @param attributes An array of strings, containing the names of the
	 *   tuple's attributes one wishes to select
	 */
	protected void setAttributeList(String[] attributes)
	{
		AttributeList al = new AttributeList();
		for (String att : attributes)
		{
			AttributeExpression aexp = null;
			if (att.contains("."))
			{
				String[] parts = att.split("\\.");
				aexp = new AttributeNameQualified(parts[0], parts[1]);
			}
			else
			{
				aexp = new AttributeNamePlain(att);
			}
			AttributeDefinition adef = new AttributeDefinitionPlain(aexp);
			al.add(adef);
		}
		m_attributeList = al;
	}
	
	public SelectFunction setProcessor(String name, Processor p)
	{
		if (m_processors == null)
		{
			m_processors = new ProcessorDefinitionList();
		}
		m_processors.add(new ProcessorDefinitionAs(name, p));
		return this;
	}

	@Override
	public Object[] compute(Object[] inputs)
	{
		if (m_aliases == null)
		{
			// This is the first time we call compute; fetch the alias names 
			// and instantiate the map with those names
			if (m_processors != null)
			{
				int size = m_processors.size();
				String[] names = new String[size];
				int i = 0;
				for (ProcessorDefinition pd : m_processors)
				{
					names[i] = pd.getAlias();
					i++;
				}
				m_aliases = new CacheMap<Object>(names);				
			}
			else
			{
				String[] names = {""};
				m_aliases = new CacheMap<Object>(names);
			}
		}
		// Fill map with current aliases
		m_aliases.putAll(inputs);
		Object[] tuples = new Object[1];
		Object t = computeCast(m_aliases);
		tuples[0] = t;
		return tuples;
	}
	
	/**
	 * Performs the computation of the SELECT on a typecast vector of
	 * inputs
	 * @param inputs A map from trace aliases to the tuple coming from 
	 *   that trace
	 * @return The output tuple
	 */
	protected Object computeCast(CacheMap<Object> inputs)
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
		if (m_builder == null)
		{
			// First tuple we build: first tell the builder what are the
			// attribute names for the output tuples
			String[] att_names = new String[m_attributeList.size()];
			int i = 0;
			for (AttributeDefinition a_def : m_attributeList)
			{
				String alias = a_def.getAlias();
				if (alias.isEmpty())
				{
					alias = a_def.getExpression().toString();
				}
				att_names[i] = alias;
				i++;
			}
			m_builder = new FixedTupleBuilder(att_names);
		}
		// Now build a tuple with the values we compute
		Object[] t_values = new Object[m_attributeList.size()];
		int i = 0;
		for (AttributeDefinition a_def : m_attributeList)
		{
			// For each attribute definition, evaluate and put its result
			// in the tuple with the given alias
			AttributeExpression a_exp = a_def.getExpression();
			Object a_result = a_exp.evaluate(inputs);
			t_values[i] = a_result;
			i++;
		}
		return m_builder.createTuple(t_values);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("SELECT ").append(m_attributeList)
			.append(" FROM ").append(m_processors);
		return out.toString();
	}
	
	@Override
	public SelectFunction clone()
	{
		SelectFunction out = new SelectFunction(getInputArity());
		out.m_aliases = m_aliases;
		out.m_attributeList = m_attributeList;
		out.m_processors = m_processors;
		return out;
	}
	
	@Override
	public int getInputArity()
	{
		// TODO Auto-generated method stub
		return m_inputArity;
	}

	@Override
	public int getOutputArity() 
	{
		// TODO Auto-generated method stub
		return 1;
	}

	@Override
	public void reset() 
	{
		// Nothing to do
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index) 
	{
		if (index < 0 || index > getInputArity())
		{
			return;
		}
		classes.add(Object.class);
	}

	@Override
	public Class<?> getOutputTypeFor(int index) 
	{
		return Connector.Variant.class;
	}
}
