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

import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.UnaryFunction;

/**
 * Given a multiset, returns a <em>new</em> multiset whose content is
 * the result of applying a function to each element.
 * 
 * @author Sylvain Hallé
 */
public class ApplyAll extends UnaryFunction<Multiset,Multiset> 
{
	/**
	 * The function to apply on each element
	 */
	protected Function m_function;
	
	public ApplyAll() 
	{
		super(Multiset.class, Multiset.class);
	}
	
	public ApplyAll(Function function)
	{
		this();
		m_function = function;
	}
	
	/**
	 * Sets the function to apply on each element
	 * @param function The condition
	 */
	public void setCondition(Function function)
	{
		m_function = function;
	}

	@Override
	public Multiset getValue(Multiset x) 
	{
		Multiset out = new Multiset();
		for (Object o : x)
		{
			Object[] in = new Object[1];
			in[0] = o;
			Object[] values = m_function.evaluate(in);
			out.add(values[0]);
		}
		return out;
	}
	
	

}
