/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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
package ca.uqac.lif.cep;

import java.util.Queue;

/**
 * Returns its input as its output. Although it seems useless,
 * <code>Passthrough</code> is used internally by the ESQL interpreter as
 * a placeholder when building processor chains from an expression.
 *  
 * @author Sylvain Hallé
 *
 */
public class Passthrough extends SingleProcessor
{
	public Passthrough(int arity)
	{
		super(arity, arity);
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		return wrapVector(inputs);
	}
	
	@Override
	public Passthrough clone()
	{
		return new Passthrough(getInputArity());
	}
}
