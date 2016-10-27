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

import java.util.Queue;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Pipe processors together using the {@link ca.uqac.lif.cep.Connector}
 * class.
 * 
 * @author Sylvain Hallé
 */
public class PipingUnary 
{
	public static void main (String[] args) throws ConnectorException
	{
		// SNIP
		QueueSource source = new QueueSource();
		source.setEvents(new Integer[]{1, 2, 3, 4, 5, 6});
		Doubler doubler = new Doubler();
		Connector.connect(source, doubler);
		Pullable p = doubler.getPullableOutput();
		for (int i = 0; i < 8; i++)
		{
			int x = (Integer) p.pull();
			System.out.println("The event is: " + x);
		}
		// SNIP
	}
	
	/**
	 * A processor that doubles every number it is given
	 */
	public static class Doubler extends SingleProcessor
	{
		public Doubler()
		{
			super(1, 1);
		}

		@Override
		protected Queue<Object[]> compute(Object[] inputs)
		{
			return wrapObject(2 * ((Number) inputs[0]).intValue());
		}

		@Override
		public Processor clone() 
		{
			return this;
		}
	}
}
