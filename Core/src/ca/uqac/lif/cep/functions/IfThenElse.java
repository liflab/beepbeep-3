/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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

import java.util.Set;

import ca.uqac.lif.cep.Connector.Variant;

/**
 * Function that acts as an if-then-else. If its first input is true,
 * it returns its second input; otherwise it returns its third input.
 * 
 * @author Sylvain Hallé
 */
public class IfThenElse extends Function
{
	/**
	 * The unique visible instance of this function
	 */
	public static final IfThenElse instance = new IfThenElse();

	protected IfThenElse()
	{
		super();
	}

	@Override
	public void evaluate(Object[] inputs, Object[] outputs)  
	{
		try
		{
			if ((Boolean) inputs[0])
			{
				outputs[0] = inputs[1];
			}
			else
			{
				outputs[0] = inputs[2];
			}
		}
		catch (ClassCastException e)
		{
			throw new InvalidArgumentException(this, 0);
		}
	}

	@Override
	public int getInputArity()
	{
		return 3;
	}

	@Override
	public int getOutputArity() 
	{
		return 1;
	}

	@Override
	public void reset() 
	{
		// Nothing to do
	}

	@Override
	public IfThenElse duplicate() 
	{
		return instance;
	}

	@Override
	public void getInputTypesFor(Set<Class<?>> classes, int index) 
	{
		if (index == 0)
		{
			classes.add(Boolean.class);
		}
		else
		{
			classes.add(Variant.class);
		}
	}

	@Override
	public Class<?> getOutputTypeFor(int index) 
	{
		return Variant.class;
	}
}
