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
import ca.uqac.lif.cep.functions.Negation;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Use the {@link ca.uqac.lif.cep.functions.FunctionProcessor} to apply
 * a function to each input event.
 * 
 * @author Sylvain Hallé
 */
public class SimpleFunction
{
	/*
	 * In this example, we apply the Negation function to a trace of
	 * Boolean values.
	 */
	public static void main (String[] args) throws ConnectorException
	{
		// SNIP
		QueueSource source = new QueueSource();
		source.setEvents(new Boolean[]{false, true, true, false, true});
		FunctionProcessor not = new FunctionProcessor(Negation.instance);
		Connector.connect(source, not);
		Pullable p = not.getPullableOutput();
		for (int i = 0; i < 5; i++)
		{
			float x = (Float) p.pull();
			System.out.println("The event is: " + x);
		}
		// SNIP
	}
}
