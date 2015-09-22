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
package ca.uqac.lif.cep.eml.numbers;

import java.util.Stack;
import java.util.Vector;

import ca.uqac.lif.cep.Buildable;
import ca.uqac.lif.cep.Combinable;

public class Sum implements Combinable
{
	public Sum()
	{
		super();
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		Sum out = new Sum();
		stack.push(out);
	}

	@Override
	public Vector<Object> initialize()
	{
		Vector<Object> ob = new Vector<Object>();
		ob.add(0);
		return ob;
	}

	@Override
	public Vector<Object> combine(Vector<Object> inputs, Vector<Object> total)
	{
		Vector<Object> ob = new Vector<Object>();
		Number n1 = (Number) total.firstElement();
		Number n2 = (Number) inputs.firstElement();
		Number n3 = n1.floatValue() + n2.floatValue();
		ob.add(n3);
		return ob;
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

	@Override
	public Buildable newInstance() 
	{
		return new Sum();
	}

}
