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
package pipes;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.numbers.Addition;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Pipe processors together using the {@link ca.uqac.lif.cep.Connector}
 * class.
 * 
 * @author Sylvain Hallé
 */
public class PipingBinary
{
	public static void main (String[] args) throws ConnectorException
	{
		// SNIP
		QueueSource source1 = new QueueSource();
		source1.setEvents(new Integer[]{2, 7, 1, 8, 3});
		QueueSource source2 = new QueueSource();
		source2.setEvents(new Integer[]{3, 1, 4, 1, 6});
		FunctionProcessor add = new FunctionProcessor(Addition.instance);
		Connector.connect(source1, 0, add, 0);
		Connector.connect(source2, 0, add, 1);
		Pullable p = add.getPullableOutput();
		for (int i = 0; i < 5; i++)
		{
			float x = (Float) p.pull();
			System.out.println("The event is: " + x);
		}
		// SNIP
	}
}
