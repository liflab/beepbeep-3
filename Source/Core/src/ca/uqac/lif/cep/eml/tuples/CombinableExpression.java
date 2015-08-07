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

import java.util.Stack;
import java.util.Vector;

import ca.uqac.lif.cep.Buildable;
import ca.uqac.lif.cep.Combinable;

public abstract class CombinableExpression implements Buildable, Combinable 
{
	protected BinaryExpression m_binaryExpression;
	
	public CombinableExpression(BinaryExpression exp)
	{
		super();
		m_binaryExpression = exp;
	}

	@Override
	public final Vector<Object> combine(Vector<Object> inputs, Vector<Object> total) 
	{
		Vector<Object> output = new Vector<Object>();
		if (inputs.size() == 0)
		{
			return total;
		}
		// Add input to total
		Object first_object = inputs.firstElement();
		Object total_object = total.firstElement();
		Object new_total = m_binaryExpression.evaluate(first_object, total_object);
		output.add(new_total);
		return output;
	}

	@Override
	public final int getInputArity() 
	{
		return 1;
	}

	@Override
	public final int getOutputArity() 
	{
		return 1;
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		stack.pop(); // combiner's name
		stack.push(this);
	}

	@Override
	public CombinableExpression newInstance()
	{
		CombinableExpression out = null;
		Class<?> c = this.getClass();
		try {
			out = (CombinableExpression) c.newInstance();
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
