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
package ca.uqac.lif.cep.math;

import java.util.Stack;
import java.util.Vector;

public class Addition extends NaryComputable
{
	public Addition()
	{
		super(2);
	}
	
	public Addition(int arity)
	{
		super(arity);
	}

	@Override
	protected Vector<Object> computeNumerical(Vector<Number> inputs)
	{
		Vector<Object> out = new Vector<Object>();
		float sum = 0;
		for (Number n : inputs)
		{
			if (n != null)
			{
				sum += n.floatValue();
			}
		}
		out.add(sum);
		return out;
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		stack.push(new Addition(2));
	}

}
