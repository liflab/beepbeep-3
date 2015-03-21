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

public abstract class Source extends SingleProcessor
{
	public Source(int out_arity)
	{
		super(0, out_arity);
	}
	
	/**
	 * Tells the source to push events into the pipeline
	 */
	public final void push()
	{
		Queue<Vector<Object>> output = compute(null);
		if (output == null || output.isEmpty())
		{
			return;
		}
		for (Vector<Object> evt : output)
		{
			if (evt != null && !evt.isEmpty())
			{
				for (int i = 0; i < output.size(); i++)
				{
					Pushable p = m_outputPushables.get(i);
					p.push(evt.get(i));
				}
			}
		}
	}
}
