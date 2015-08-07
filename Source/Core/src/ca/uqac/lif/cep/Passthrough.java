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
 * The passthrough processor returns its input as its output
 * @author sylvain
 *
 */
public class Passthrough extends SingleProcessor
{
	public Passthrough(int arity)
	{
		super(arity, arity);
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		return wrapVector(inputs);
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		int arity = getInputArity();
		Passthrough out = new Passthrough(arity);
		for (int i = 0; i < arity; i++)
		{
			Processor p = (Processor) stack.pop();
			Connector.connect(p,  out,  1,  i);
		}
		stack.push(out);
	}
	
	@Override
	public Passthrough newInstance()
	{
		return new Passthrough(getInputArity());
	}


}
