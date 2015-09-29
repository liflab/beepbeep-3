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

public class Subtraction extends NaryComputable
{
	public Subtraction()
	{
		super(2);
	}

	@Override
	protected Object[] computeNumerical(Number[] inputs)
	{
		Object[] out = new Object[1];
		float diff = 0;
		if (inputs.length >= 2)
		{
			Number n1 = inputs[0];
			Number n2 = inputs[inputs.length - 1];
			diff = n2.floatValue() - n1.floatValue();
		}
		out[0] = diff;
		return out;
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		stack.push(new Subtraction());
	}

}
