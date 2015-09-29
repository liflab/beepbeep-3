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

import ca.uqac.lif.cep.Processor;

public class IsEven extends NaryComputable
{
	public IsEven()
	{
		super(1);
	}

	@Override
	protected Object[] computeNumerical(Number[] inputs)
	{
		Object[] out = new Object[1];
		if (Processor.allNull(inputs))
		{
			out[0] = false;
		}
		else
		{
			Number n = inputs[0];
			if (n.intValue() % 2 == 0)
			{
				out[0] = true;
			}
			else
			{
				out[0] = false;
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
