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
import java.util.Stack;
import java.util.Vector;

/**
 * Duplicates an input event into two or more output events
 * @author sylvain
 *
 */
public class Fork extends SingleProcessor
{
	public Fork(int out_arity)
	{
		super(1, out_arity);
	}
	
	/**
	 * Creates a copy of the current fork with a greater arity
	 * @param out_arity The desired arity for the output fork
	 */
	public void extendArity(int out_arity)
	{
		m_outputArity = out_arity;
		reset();
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		int arity = getOutputArity();
		Vector<Object> out = new Vector<Object>(arity);
		if (!inputs.isEmpty())
		{
			Object o = inputs.firstElement();
			for (int i = 0; i < arity; i++)
			{
				out.add(o);
			}
		}
		return wrapVector(out);
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		// TODO
	}
	
	@Override
	public Fork newInstance()
	{
		return new Fork(getOutputArity());
	}

}
