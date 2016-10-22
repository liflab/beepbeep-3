/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hall�

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
package queries;

import static ca.uqac.lif.cep.Connector.connect;
import static ca.uqac.lif.cep.Connector.INPUT;
import static ca.uqac.lif.cep.Connector.LEFT;
import static ca.uqac.lif.cep.Connector.OUTPUT;
import static ca.uqac.lif.cep.Connector.RIGHT;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.numbers.IsEven;
import ca.uqac.lif.cep.tmf.Filter;
import ca.uqac.lif.cep.tmf.Fork;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Filter a trace by evaluating a simple condition on the events of
 * that trace.
 * 
 * @author Sylvain Hallé
 */
public class FilterConditionSimple
{
	public static void main(String[] args) throws ConnectorException
	{
		// Create a trace of dummy values
		QueueSource source_values = new QueueSource();
		source_values.setEvents(new Integer[]{6, 5, 3, 8, 9, 2, 1, 7, 4});
		// Fork the trace in two
		Fork fork = new Fork(2);
		connect(source_values, fork);
		// Connect the first ("left") output of the fork into a filter
		Filter filter = new Filter();
		connect(fork, LEFT, filter, LEFT);
		// Create a processor evaluating the function "is even"
		FunctionProcessor condition = new FunctionProcessor(IsEven.instance);
		// Connect its input to the second output of the fork
		connect(fork, RIGHT, condition, INPUT);
		// Connect the condition as the second input of our filter
		connect(condition, OUTPUT, filter, RIGHT);
		// Get a reference to the filter's output pullable
		Pullable p = filter.getPullableOutput();
		// Pull 4 events from p. This will only output even events, and
		// discard odd numbers
		for (int i = 0; i < 4; i++)
		{
			int x = (Integer) p.pull();
			System.out.printf("Output event #%d is %d\n", i, x);
		}


	}
}
