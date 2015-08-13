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
package ca.uqac.lif.cep.ltl;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.eml.tuples.EmlBoolean;

public abstract class UnaryProcessor extends SingleProcessor 
{
	public UnaryProcessor()
	{
		super(1, 1);
	}

	@Override
	protected final Queue<Vector<Object>> compute(Vector<Object> inputs) 
	{
		Object o = inputs.firstElement();
		if (o == null)
		{
			return new LinkedList<Vector<Object>>();
		}
		EmlBoolean result = compute(EmlBoolean.toEmlBoolean(o));
		if (result == null)
		{
			return null;
		}
		Vector<Object> out = new Vector<Object>();
		out.add(result);
		return wrapVector(out);
	}
	
	protected abstract EmlBoolean compute(EmlBoolean input);

	@Override
	public void build(Stack<Object> stack) 
	{
		stack.pop(); // (
		Processor p = (Processor) stack.pop();
		stack.pop(); // )
		stack.pop(); // G
		Connector.connect(p,  this);
		stack.push(this);
	}
}
