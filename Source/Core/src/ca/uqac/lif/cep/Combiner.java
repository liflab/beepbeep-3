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

public class Combiner extends SingleProcessor
{
	protected Vector<Object> m_total = null;
	
	protected Combinable m_combinable = null;
	
	public Combiner()
	{
		super();
	}
	
	public Combiner(Combinable combinable)
	{
		super(combinable.getInputArity(), combinable.getOutputArity());
		m_combinable = combinable;
		m_total = m_combinable.initialize();
	}
	
	@Override
	public void reset()
	{
		super.reset();
		if (m_combinable != null)
		{
			m_total = m_combinable.initialize();
		}
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		m_total = m_combinable.combine(inputs, m_total);
		return wrapVector(m_total);
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		Combinable com = (Combinable) stack.pop();
		stack.pop(); // WITH
		stack.pop(); // )
		Processor p = (Processor) stack.pop();
		stack.pop(); // (
		stack.pop(); // COMBINE
		Combiner out = new Combiner(com);
		Connector.connect(p, out);
		stack.push(out);
	}

}
