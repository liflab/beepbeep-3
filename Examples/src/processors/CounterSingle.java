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
package processors;
import static ca.uqac.lif.cep.Connector.OUTPUT;

import java.util.ArrayDeque;
import java.util.Queue;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * This processor simply generates the trace of numbers 0, 1, 2, ...
 * This is one of two possible ways of writing such a counter: by
 * creating an instance of SingleProcessor with a purpose-built
 * <code>compute()</code> method. Another way is illustrated by the
 * {@link CounterGroup} class.
 */
public class CounterSingle extends SingleProcessor
{
	/**
	 * The variable that will keep the current value of the counter
	 */
	protected int m_counterValue;
	
	/*
	 * The constructor sets the input and output arity of this processor.
	 * The input arity is 0, as we do not need an input trace to
	 * generate something. The output arity is 1, as we output one trace
	 * of numbers.
	 * 
	 * As for any other object, the constructor is also responsible of
	 * setting the initial state; in our case, this means setting our
	 * counter variable to 1.
	 */
	public CounterSingle() 
	{
		super(0, 1);
		m_counterValue = 1;
	}

	/*
	 * This is where the actual processing occurs. Method compute() is
	 * called every time a new output event must be generated.
	 */
	@Override
	protected Queue<Object[]> compute(Object[] inputs) 
	{
		// Create a queue of Object[]. We must put our
		// results in this queue and return it at the end
		Queue<Object[]> out_queue = new ArrayDeque<Object[]>();

		// Create an array of objects of size 1
		Object[] front = new Object[1];
		
		// Put into this array the current value of our counter,
		// and then increment this counter
		front[0] = m_counterValue;
		m_counterValue++;
		
		// Put the array in the queue
		out_queue.add(front);

		// Return the queue
		return out_queue;
	}

	/*
	 * We must implement method clone() so that BeepBeep
	 * can make copies of this processor if needed. This would occur,
	 * for example, if MyCounter were the argument of a
	 * WindowProcessor. In our case, cloning simply amounts to
	 * returning a new instance of MyCounter.
	 */
	@Override
	public Processor clone() 
	{
		return new CounterSingle();
	}

	/*
	 * Simple main showing what the processor does. It should output the numbers 1 to 10.
	 */
	public static void main(String[] args)
	{
		CounterGroup counter = new CounterGroup();
		Pullable p = counter.getPullableOutput(OUTPUT);
		for (int i = 0; i < 10; i++)
		{
			float n = (float) p.pullHard();
			System.out.println(n);
		}
	}
}
