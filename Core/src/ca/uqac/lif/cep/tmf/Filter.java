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

import ca.uqac.lif.cep.SingleProcessor;

/**
 * Discards events from an input trace based on a selection criterion.
 * The processor takes as input two events simultaneously; it outputs
 * the first if the second is true.
 * 
 * @author Sylvain Hallé
 */
@SuppressWarnings("squid:S2160")
public class Filter extends SingleProcessor
{
	public Filter()
	{
		super(2, 1);
	}

	@Override
	@SuppressWarnings("squid:S3516")
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		Object o = inputs[0];
		Object[] out = new Object[1];
		boolean b = (Boolean) inputs[inputs.length - 1];
		if (b)
		{
			out[0] = o;
		}
		else
		{
			return true;
		}
		outputs.add(out);
		return true;
	}

	@Override
	public Filter duplicate()
	{
		return new Filter();
	}
}
