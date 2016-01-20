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
package ca.uqac.lif.cep.eml.tuples;


import ca.uqac.lif.cep.SingleProcessor;

public abstract class Tuple extends SingleProcessor
{
	public Tuple()
	{
		super(0, 1);
	}
	
	public static Object computeWrap(Object o, Object[] inputs)
	{
		if (o instanceof Tuple)
		{
			// o is a tuple: call its compute method
			return ((Tuple) o).compute(inputs);
		}
		// o is an instance of a Java object (non-tuple): return it
		return o;
	}
}
