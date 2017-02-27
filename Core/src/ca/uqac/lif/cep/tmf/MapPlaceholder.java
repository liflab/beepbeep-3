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

import java.util.ArrayDeque;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.ArgumentPlaceholder;
import ca.uqac.lif.cep.util.CacheMap;

public class MapPlaceholder extends ArgumentPlaceholder
{
	public MapPlaceholder(int index)
	{
		super(index);
	}

	public static void build(ArrayDeque<Object> stack)
	{
		Object o = stack.pop();
		if (o instanceof String)
		{
			// Remove first character
			String s = (String) o;
			int pos = -1;
			try
			{
				// It's a number
				pos = Integer.parseInt(s.substring(1));
				stack.push(new MapPlaceholder(pos));
				return;
			}
			catch (NumberFormatException e)
			{
				// It's a string
				stack.push(new NamedMapPlaceholder(s));
			}
		}
		else if (o instanceof Number)
		{
			int pos = ((Number) o).intValue();
			stack.push(new MapPlaceholder(pos));
			return;
		}
		else
		{
			// Not supposed to happen
			assert false;
		}
	}

	@Override
	public void evaluate(Object[] inputs, Object[] out, Context context)
	{
		@SuppressWarnings("unchecked")
		CacheMap<Object> map = (CacheMap<Object>) inputs[0];
		out[0] = map.getValue(getIndex());
	}
}
