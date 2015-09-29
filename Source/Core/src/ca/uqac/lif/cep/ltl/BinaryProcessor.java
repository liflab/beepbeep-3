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

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.eml.tuples.EmlBoolean;

public abstract class BinaryProcessor extends SingleProcessor 
{
	public BinaryProcessor()
	{
		super(2, 1);
	}

	@Override
	protected final Queue<Object[]> compute(Object[] inputs) 
	{
		Object left = inputs[0];
		Object right = inputs[1];
		if (left == null || right == null)
		{
			return new LinkedList<Object[]>();
		}
		EmlBoolean result = compute(EmlBoolean.toEmlBoolean(left), EmlBoolean.toEmlBoolean(right));
		if (result == null)
		{
			return null;
		}
		Object[] out = new Object[1];
		out[0] = result;
		return wrapVector(out);
	}
	
	protected abstract EmlBoolean compute(EmlBoolean left, EmlBoolean right);

	@Override
	public void build(Stack<Object> stack) 
	{
		stack.pop(); // (
		Processor right = (Processor) stack.pop();
		stack.pop(); // )
		stack.pop(); // op
		stack.pop(); // (
		Processor left = (Processor) stack.pop();
		stack.pop(); // )
		Connector.connect(left, this, 0, 0);
		Connector.connect(right, this, 0, 1);
		stack.push(this);
	}
}
