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
package pipes;

import static ca.uqac.lif.cep.Connector.connect;
import static ca.uqac.lif.cep.Connector.LEFT;
import static ca.uqac.lif.cep.Connector.OUTPUT;
import static ca.uqac.lif.cep.Connector.RIGHT;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.tmf.Filter;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Discard events from an input trace with the 
 * {@link ca.uqac.lif.cep.tmf.Filter} processor.
 *  
 * @author Sylvain Hallé
 */
public class FilterSimple 
{
	public static void main(String[] args) throws ConnectorException 
	{
		// Create a first trace of dummy values
		QueueSource source_values = new QueueSource();
		source_values.setEvents(new Integer[]{6, 5, 3, 8, 9, 2, 1, 7, 4});
		// Create a second trace of Boolean values
		QueueSource source_bool = new QueueSource();
		source_bool.setEvents(new Boolean[]{true, false, true, true,
				false, false, true, false, true});
		// Create a filter
		Filter filter = new Filter();
		// Connect both to the filter
		connect(source_values, OUTPUT, filter, LEFT);
		connect(source_bool, OUTPUT, filter, RIGHT);
		// Get a reference to the filter's output pullable
		Pullable p = filter.getPullableOutput();
		// Pull 5 events from p
		for (int i = 0; i < 5; i++)
		{
			int x = (Integer) p.pull();
			System.out.printf("Output event #%d is %d\n", i, x);
		}
	}

}
