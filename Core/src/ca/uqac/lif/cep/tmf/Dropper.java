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
package ca.uqac.lif.cep.tmf;

import java.util.Queue;
import java.util.Set;

import ca.uqac.lif.cep.SingleProcessor;

/**
 * Takes a set of elements as input, and returns as many output
 * events as there are elements in that set.
 * 
 * @author Sylvain Hallé
 */
public class Dropper extends SingleProcessor
{
	public Dropper()
	{
		super(1, 1);
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		Object o = inputs[0];
		if (o instanceof Set)
		{
			Set<?> s_o = (Set<?>) o;
			for (Object obj : s_o)
			{
				Object[] obj_array = new Object[1];
				obj_array[0] = obj;
				outputs.add(obj_array);
			}
			return true;
		}
		else
		{
			outputs.add(wrapObject(o));
			return true;
		}
	}

	@Override
	public Dropper duplicate()
	{
		return new Dropper();
	}


}
