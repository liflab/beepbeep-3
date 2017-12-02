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

import java.util.Set;

import ca.uqac.lif.cep.Connector.Variant;

public abstract class Variable extends Function 
{	
	/**
	 * Creates a new placeholder
	 */
	public Variable()
	{
		super();
	}
	
	@Override
	public void evaluate(Object[] inputs, Object[] outputs)
	{
		evaluate(inputs, outputs, null);
	}

	@Override
	public int getInputArity()
	{
		return 0;
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
	public void getInputTypesFor(Set<Class<?>> classes, int index)
	{
		classes.add(Variant.class);
	}

	@Override
	public Class<?> getOutputTypeFor(int index)
	{
		return Variant.class;
	}
}
