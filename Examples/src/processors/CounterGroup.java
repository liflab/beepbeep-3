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

import static ca.uqac.lif.cep.Connector.INPUT;
import static ca.uqac.lif.cep.Connector.OUTPUT;
import static ca.uqac.lif.cep.Connector.connect;

import java.util.Vector;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.CumulativeProcessor;
import ca.uqac.lif.cep.numbers.Addition;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * This processor simply generates the trace of numbers 0, 1, 2, ...
 * This is one of two possible ways of writing such a counter: by
 * encapsulating a <code>CumulativeProcessor</code> within a
 * <code>GroupProcessor</code>. Another way is illustrated by the
 * {@link CounterSingle} class.
 */
public class CounterGroup extends GroupProcessor
{
	public CounterGroup()
	{
		super(0, 1);
		// Now create a source of 1s and sum it; this
		// effectively creates a counter outputting 1, 2, ...
		Vector<Object> one_list = new Vector<Object>();
		one_list.add(1);
		QueueSource ones = new QueueSource();
		ones.setEvents(one_list);
		CumulativeProcessor counter = new CumulativeProcessor(new CumulativeFunction<Number>(Addition.instance));
		try
		{
			connect(ones, OUTPUT, counter, INPUT);
		}
		catch (ConnectorException e)
		{
			// This is not supposed to happen; we know what we're doing!
		}
		// Adds the processors we created to the group
		addProcessors(ones, counter);
		// Associate the output of the group to the output of counter
		associateOutput(OUTPUT, counter, OUTPUT);
		// This processor has no input; otherwise, we would also need to
		// associate the input of the group to the input of some processor
	}

	/*
	 * Simple main showing what the processor does. It should output the numbers 1 to 10.
	 */
	public static void main(String[] args)
	{
		CounterGroup counter = new CounterGroup();
		Pullable p = counter.getPullableOutput();
		for (int i = 0; i < 10; i++)
		{
			float n = (Float) p.pull();
			System.out.println(n);
		}
	}
}
