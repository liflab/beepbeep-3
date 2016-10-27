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
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.functions.FunctionProcessor;
import ca.uqac.lif.cep.functions.Negation;
import ca.uqac.lif.cep.numbers.AbsoluteValue;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * What happens when you pipe processors with non-matching event
 * types.
 * 
 * @author Sylvain Hallé
 */
public class IncorrectPiping 
{
	public static void main(String[] args) throws ConnectorException
	{
		// SNIP
		QueueSource source = new QueueSource();
		source.setEvents(new Integer[]{3});
		Processor av = new FunctionProcessor(AbsoluteValue.instance);
		Connector.connect(source, av);
		Processor neg = new FunctionProcessor(Negation.instance);
		Connector.connect(av, neg); // Will throw an exception
		System.out.println("This line will not be reached");
		// SNIP
	}
}
