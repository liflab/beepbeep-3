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
package queries;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.CumulativeProcessor;
import ca.uqac.lif.cep.numbers.Addition;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Use a cumulative processor to compute the sum of all events
 * received so far. 
 * 
 * @author Sylvain Hallé
 */
public class CumulativeSum 
{
	public static void main(String[] args) throws ConnectorException
	{
		// SNIP
		QueueSource source = new QueueSource();
		source.setEvents(new Integer[]{1, 2, 3, 4, 5, 6});
		CumulativeProcessor sum = new CumulativeProcessor(
				new CumulativeFunction<Number>(Addition.instance));
		Connector.connect(source, sum);
		// SNIP
		Pullable p = sum.getPullableOutput();
		for (int i = 0; i < 5; i++)
		{
			float x = (Float) p.pull();
			System.out.println("The event is: " + x);
		}
	}

}
