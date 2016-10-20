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
package ca.uqac.lif.cep.sets;

import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Gets all the elements of the multiset that satisfy some condition.
 * This condition is specified as an unary function that is successively
 * applied to each element of the multiset; if the function returns
 * <tt>true</tt>, the element is added to the output result, otherwise it
 * is discarded.
 * 
 * @author Sylvain Hallé
 */
public class GetElements extends UnaryFunction<Multiset,Multiset> 
{
	/**
	 * The condition to evaluate on each element
	 */
	protected UnaryFunction<Object,Boolean> m_condition;
	
	public GetElements() 
	{
		super(Multiset.class, Multiset.class);
	}
	
	public GetElements(UnaryFunction<Object,Boolean> condition)
	{
		this();
		m_condition = condition;
	}
	
	/**
	 * Sets the condition to evaluate on each element
	 * @param condition The condition
	 */
	public void setCondition(UnaryFunction<Object,Boolean> condition)
	{
		m_condition = condition;
	}

	@Override
	public Multiset getValue(Multiset x) 
	{
		Multiset out = new Multiset();
		for (Object o : x)
		{
			Object[] in = new Object[1];
			in[0] = o;
			Object[] values = m_condition.evaluate(in);
			if (values[0] instanceof Boolean && ((Boolean) values[0]))
			{
				out.add(o);
			}
		}
		return out;
	}
	
	

}
