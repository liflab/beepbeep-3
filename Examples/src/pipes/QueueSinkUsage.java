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

import java.util.Queue;

import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.tmf.QueueSink;

/**
 * Push events into a {@link ca.uqac.lif.cep.tmf.QueueSink}
 * processor.
 * 
 * @author Sylvain Hallé
 */
public class QueueSinkUsage
{
	public static void main(String[] args)
	{
		// Create a sink
		QueueSink sink = new QueueSink();
		// Get a reference to the sink's Pushable
		Pushable p = sink.getPushableInput();
		// Push a few events into the sink
		p.push("foo");
		p.push("bar");
		// Get a reference to the sink's queue, where events are stored
		Queue<Object> queue = sink.getQueue();
		System.out.println("Events in the sink: " + queue);
		// Events remain in the queue as long as you pop them out
		queue.remove(); // Removes the first event
		p.push("baz"); // Push another one
		System.out.println("Events in the sink: " + queue);
	}

}
