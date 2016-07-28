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
package ca.uqac.lif.cep.fol;

import ca.uqac.lif.cep.fol.Predicate.PredicateArgument;
import ca.uqac.lif.cep.util.Arrays;

/**
 * An assertion defining the truth value of a predicate
 * for a concrete list of arguments.
 * <p>
 * For example, the
 * predicate tuple <i>p</i>(b,0) = TRUE stipulates that
 * predicate <i>p</i>, when given the arguments "b" (a constant) and 0,
 * returns the value TRUE. 
 */
public class PredicateTuple
{
	/**
	 * The arguments of this predicate tuple
	 */
	protected PredicateArgument m_arguments;

	/**
	 * The value associated to these arguments
	 */
	protected boolean m_value;

	/**
	 * The name of the predicate this tuple defines
	 */
	protected String m_name;

	/**
	 * Creates a new predicate tuple
	 * @param name The name of the predicate this tuple defines
	 * @param value The value associated to the arguments
	 * @param arguments The arguments of this predicate tuple
	 */
	public PredicateTuple(String name, boolean value, Object[] arguments)
	{
		super();
		m_name = name;
		m_arguments = new PredicateArgument(arguments);
		m_value = value;
	}

	/**
	 * Gets the name of the predicate this tuple defines
	 * @return The name
	 */
	public String getName()
	{
		return m_name;
	}

	/**
	 * Retrieves the <i>n</i>-th argument of the tuple
	 * @param index The position to retrieve
	 * @return The value, or <code>null</code> if index is out of bounds
	 */
	public Object getArgument(int index)
	{
		return m_arguments.get(index);
	}

	/**
	 * Creates a predicate tuple out of an object.
	 * @param x An array or an ordered collection of objects.
	 * Null elements and strings consisting only of whitespace,
	 * will be ignored when creating the tuple. 
	 * @return The tuple
	 */
	public static PredicateTuple toPredicateTuple(Object x)
	{
		Object[] contents = Arrays.toObjectArray(x);
		String name = (String) contents[0];
		int num_non_empty = 0;
		for (int i = 1; i < contents.length; i++)
		{
			// Trim all strings and count non-null and non-empty elements
			if (contents[i] != null)
			{
				String trimmed = ((String) contents[i]).trim();
				contents[i] = trimmed;
				if (!trimmed.isEmpty())
				{
					num_non_empty++;
				}
				else
				{
					contents[i] = null;
				}
			}
		}
		Object[] arg_vals = new Object[num_non_empty];
		for (int i = 1, index = 0; i < contents.length; i++)
		{
			if (contents[i] != null)
			{
				arg_vals[index++] = contents[i];
			}
		}
		PredicateTuple tuple = new PredicateTuple(name, true, arg_vals);
		return tuple;
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append(m_name).append("(").append(m_arguments).append(")");
		return out.toString();
	}

}