package queries;
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
import java.util.Vector;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.CumulativeProcessor;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.numbers.Addition;
import ca.uqac.lif.cep.numbers.Division;
import ca.uqac.lif.cep.tmf.QueueSource;
import static ca.uqac.lif.cep.Connector.LEFT;
import static ca.uqac.lif.cep.Connector.RIGHT;
import static ca.uqac.lif.cep.Connector.INPUT;
import static ca.uqac.lif.cep.Connector.OUTPUT;
import static ca.uqac.lif.cep.Connector.connect;


/**
 * Compute the cumulative average of a list of
 * numbers. The cumulative average is the average of all the numbers
 * processed so far.
 * <p>
 * Represented graphically, this example corresponds to the following chain
 * of processors:
 * <p>
 * <img src="{@docRoot}/doc-files/Average.png" alt="Processor graph">
 * 
 * @author Sylvain Hallé
 *
 */
public class Average 
{

	public static void main(String[] args) throws ConnectorException 
	{
		// Create a source of numbers
		QueueSource numbers = new QueueSource(1);
		numbers.setEvents(new Object[]{2, 7, 1, 8, 2, 8, 1, 8, 2, 8,
				4, 5, 9, 0, 4, 5, 2, 3, 5, 3, 6, 0, 2, 8, 7});
		// Pipe the output of this processor to a cumulative processor that
		// computes the cumulative sum of numbers
		CumulativeProcessor sum_proc = new CumulativeProcessor(new CumulativeFunction<Number>(Addition.instance));
		connect(numbers, OUTPUT, sum_proc, INPUT);

		// Now create a source of 1s and sum it; this
		// effectively creates a counter outputting 1, 2, ...
		Vector<Object> one_list = new Vector<Object>();
		one_list.add(1);
		QueueSource ones = new QueueSource(1);
		ones.setEvents(one_list);
		CumulativeProcessor counter = new CumulativeProcessor(new CumulativeFunction<Number>(Addition.instance));
		connect(ones, OUTPUT, counter, INPUT);
		
		// Divide one trace by the other; the output is the cumulative average
		// of all numbers seen so far
		FunctionProcessor division = new FunctionProcessor(Division.instance);
		connect(sum_proc, OUTPUT, division, LEFT);
		connect(counter, OUTPUT, division, RIGHT);
		
		// Extract the first 20 events from that pipe and print them
		Pullable p = division.getPullableOutput();
		System.out.println("The cumulative average is...");
		for (int i = 0; i < 20; i++)
		{
			float value = (float) p.pull();
			System.out.print(value + ", ");
		}
		System.out.println("done!");
	}
}
