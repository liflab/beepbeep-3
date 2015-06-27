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
package ca.uqac.lif.cep;

import java.util.Queue;
import java.util.Vector;

/**
 * Discards events from an input trace based on a selection criterion.
 * The processor takes as input two events simultaneously; it outputs
 * the first if the second is true.
 * @author sylvain
 *
 */
public class Filter extends SingleProcessor
{
	public Filter()
	{
		super(2, 1);
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		Object o = inputs.firstElement();
		Vector<Object> out = new Vector<Object>();
		boolean b = (Boolean) inputs.lastElement();
		if (b)
		{
			out.add(o);
		}
		return wrapVector(out);
	}

}
