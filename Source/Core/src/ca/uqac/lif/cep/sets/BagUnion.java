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
package ca.uqac.lif.cep.sets;

import java.util.Stack;

import ca.uqac.lif.cep.Buildable;
import ca.uqac.lif.cep.Combinable;

public class BagUnion implements Combinable
{
	public BagUnion()
	{
		super();
	}

	@Override
	public void build(Stack<Object> stack)
	{
		stack.pop(); // UNION
		stack.pop(); // BAG
		stack.push(this);
	}

	@Override
	public Buildable newInstance() 
	{
		return new BagUnion();
	}

	@Override
	public Object[] initialize()
	{
		Object[] out_vector = new Object[1];
		out_vector[0] = new EmlBag();
		return out_vector;
	}

	@Override
	public Object[] combine(Object[] inputs, Object[] total) 
	{
		Object[] out_vector = new Object[getOutputArity()];
		EmlBag total_bag = (EmlBag) total[0];
		for (Object o : inputs)
		{
			if (o instanceof EmlBag)
			{
				EmlBag in_bag = (EmlBag) o;
				total_bag.addAll(in_bag);
			}
		}
		out_vector[0] =  total_bag;
		return out_vector;
	}

	@Override
	public int getInputArity() 
	{
		return 1;
	}

	@Override
	public int getOutputArity() 
	{
		return 1;
	}

}
