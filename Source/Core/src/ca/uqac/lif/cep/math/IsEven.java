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

public class IsEven extends NaryComputable
{
	public IsEven()
	{
		super(1);
	}

	@Override
	protected Vector<Object> computeNumerical(Vector<Number> inputs)
	{
		Vector<Object> out = new Vector<Object>();
		if (inputs.isEmpty())
		{
			out.add(false);
		}
		else
		{
			Number n = inputs.firstElement();
			if (n.intValue() % 2 == 0)
			{
				out.add(true);
			}
			else
			{
				out.add(false);
			}
		}
		return out;
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		stack.push(new IsEven());
	}

}
