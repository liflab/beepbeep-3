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
package ca.uqac.lif.cep.functions;

import java.util.Set;

import ca.uqac.lif.cep.Context;

/**
 * A tree of n-ary functions composed together
 * @author Sylvain Hallé
 */
public class FunctionTree extends Function 
{
	/**
	 * The function to evaluate
	 */
	protected Function m_function;
	
	/**
	 * The children function to evaluate first
	 */
	protected Function[] m_children;
	
	/**
	 * Creates a new function tree
	 * @param f The function to act as the root of the tree
	 */
	public FunctionTree(Function f)
	{
		super();
		m_function = f;
		m_children = new Function[f.getInputArity()];
	}
	
	/**
	 * Creates a new function tree, by specifying the root and
	 * its immediate children
	 * @param functions An array of functions. The first element
	 *   of the array is the function to act as the root of the tree. The
	 *   size of the array must be <i>n</i>+1, where <i>n</i> is the
	 *   input arity of that function. The remaining elements of the
	 *   array are the functions that will be the children of the root
	 *   in the resulting tree.
	 */
	public FunctionTree(Function ... functions)
	{
		this(functions[0]);
		for (int i = 1; i < functions.length; i++)
		{
			setChild(i - 1, functions[i]);
		}
	}
	
	/**
	 * Sets the <i>i</i>-th child of the tree
	 * @param index The index
	 * @param f The function
	 * @return This tree
	 */
	public FunctionTree setChild(int index, Function f)
	{
		if (index >= 0 && index < m_children.length)
		{
			m_children[index] = f;
		}
		return this;
	}
	
	@Override
	public Object[] evaluate(Object[] inputs, Context context)
	{
		Object[] values = new Object[m_children.length];
		for (int i = 0; i < values.length; i++)
		{
			values[i] = m_children[i].evaluate(inputs, context)[0];
		}
		return m_function.evaluate(values, context);
	}
	
	@Override
	public Object[] evaluate(Object[] inputs)
	{
		return evaluate(inputs, null);
	}

	@Override
	public int getInputArity()
	{
		int max_arity = 0;
		for (Function child : m_children)
		{
			if (child instanceof ArgumentPlaceholder)
			{
				max_arity = Math.max(max_arity, ((ArgumentPlaceholder) child).getIndex() + 1);
			}
			else
			{
				max_arity = Math.max(max_arity, child.getInputArity());
			}
		}
		return max_arity;
		//return m_function.getInputArity();
	}

	@Override
	public int getOutputArity() 
	{
		return m_function.getOutputArity();
	}

	@Override
	public void reset() 
	{
		m_function.reset();
		for (Function f : m_children)
		{
			f.reset();
		}

	}

	@Override
	public FunctionTree clone() 
	{
		FunctionTree out = new FunctionTree(m_function.clone());
		for (int i = 0; i < m_children.length; i++)
		{
			out.m_children[i] = m_children[i].clone();
		}
		return out;
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index) 
	{
		m_function.getInputTypesFor(classes, index);
	}

	@Override
	public Class<?> getOutputTypeFor(int index) 
	{
		return m_function.getOutputTypeFor(index);
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		if (m_children.length == 2)
		{
			out.append("[").append(m_children[0]).append("]").append(m_function).append("[").append(m_children[1]).append("]");
		}
		else
		{
			out.append(m_function).append("[");
			for (int i = 0; i < m_children.length; i++)
			{
				if (i > 0)
				{
					out.append(",");
				}
				out.append(m_children[i]);
			}
			out.append("]");
		}
		return out.toString();
	}
	
	@Override
	public void setContext(Context context)
	{
		super.setContext(context);
		m_function.setContext(context);
		for (Function f : m_children)
		{
			f.setContext(context);
		}
	}
	
	@Override
	public void setContext(String key, Object value)
	{
		super.setContext(key, value);
		m_function.setContext(key, value);
		for (Function f : m_children)
		{
			f.setContext(key, value);
		}
	}
}
