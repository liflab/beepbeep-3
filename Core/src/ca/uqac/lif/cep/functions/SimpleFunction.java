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
package ca.uqac.lif.cep.functions;

import ca.uqac.lif.cep.Context;

public abstract class SimpleFunction extends Function
{
	@Override
	public Object[] evaluate(Object[] inputs, Context context)
	{
		// If no context is given, call compute() straight away
		if (context == null)
		{
			return compute(inputs);
		}
		Object[] concrete_inputs = new Object[inputs.length];
		// Check each of the concrete inputs if it is a placeholder
		for (int i = 0; i < inputs.length; i++)
		{
			Object argument = inputs[i];
			if (argument instanceof ContextPlaceholder)
			{
				// If so, fetch concrete object in context
				ContextPlaceholder ap = (ContextPlaceholder) argument;
				String ap_name = ap.getName();
				if (context.containsKey(ap_name))
				{
					concrete_inputs[i] = context.get(ap_name);
				}
				else
				{
					// If we didn't find the value in the context, leave the argument
					// as is and hope the function will know what to do with it
					concrete_inputs[i] = argument;
				}
			}
			else
			{
				concrete_inputs[i] = argument;
			}
		}
		// Call compute() with concrete inputs
		return compute(concrete_inputs);
	}
	
	@Override
	public Object[] evaluate(Object[] inputs)
	{
		return compute(inputs);
	}

	/**
	 * Computes the outputs of the function, given some inputs
	 * @param inputs The arguments of the function. The size of the array
	 *   should be equal to the function's declared input arity.
	 * @return The outputs of the function. The size of the array returned
	 *   should be equal to the function's declared output arity.
	 */
	public abstract Object[] compute(Object[] inputs);
}
