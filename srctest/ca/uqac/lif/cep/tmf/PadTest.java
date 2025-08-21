/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2019 Sylvain Hallé

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
package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.*;

import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pushable;

public class PadTest
{
  @Test
  public void test1Push()
  {
    Pad pad = new Pad(new Passthrough(), 2, -1);
    QueueSink sink = new QueueSink();
    Connector.connect(pad, sink);
    Pushable p = pad.getPushableInput();
    Queue<Object> queue = sink.getQueue();
    p.push("A");
    assertFalse(queue.isEmpty());
    assertEquals(-1, queue.remove());
    p.push("B");
    assertFalse(queue.isEmpty());
    assertEquals(-1, queue.remove());
    p.push("C");
    assertFalse(queue.isEmpty());
    assertEquals("A", queue.remove());
    assertFalse(queue.isEmpty());
    assertEquals("B", queue.remove());
    assertFalse(queue.isEmpty());
    assertEquals("C", queue.remove());
  }
}
