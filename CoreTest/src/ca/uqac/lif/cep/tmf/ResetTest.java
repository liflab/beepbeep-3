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
package ca.uqac.lif.cep.tmf;

import static org.junit.Assert.*;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.functions.Cumulate;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.util.Numbers;
import org.junit.Test;

/**
 * Unit tests for the {@link ResetLast} processor.
 */
public class ResetTest
{
  @Test
  public void test1()
  {
    Passthrough pt = new Passthrough();
    ResetLast reset = new ResetLast(pt);
    QueueSource src1 = new QueueSource().setEvents(true, false, false, true, false).loop(false);
    QueueSource src2 = new QueueSource().setEvents(1, 2, 3, 4, 5).loop(false);
    Connector.connect(src2, 0, reset, 0);
    Connector.connect(src1, 0, reset, 1);
    Pullable p = reset.getPullableOutput();
    assertEquals(1, p.pull());
    assertEquals(4, p.pull());
    assertFalse(p.hasNext());
  }
  
  @Test
  public void test2()
  {
    Cumulate sum = new Cumulate(new CumulativeFunction<Number>(Numbers.addition));
    ResetLast reset = new ResetLast(sum);
    QueueSource src1 = new QueueSource().setEvents(true, false, false, true, false).loop(false);
    QueueSource src2 = new QueueSource().setEvents(1, 2, 3, 4, 5).loop(false);
    Connector.connect(src2, 0, reset, 0);
    Connector.connect(src1, 0, reset, 1);
    Pullable p = reset.getPullableOutput();
    assertEquals(1f, p.pull());
    assertEquals(9f, p.pull());
    assertFalse(p.hasNext());
  }
  
  @Test
  public void test3()
  {
    Cumulate sum = new Cumulate(new CumulativeFunction<Number>(Numbers.addition));
    ResetLast reset = new ResetLast(sum);
    QueueSource src1 = new QueueSource().setEvents(true, false, false, true, false, false, true).loop(false);
    QueueSource src2 = new QueueSource().setEvents(1, 2, 3, 4, 5, 6, 7).loop(false);
    Connector.connect(src2, 0, reset, 0);
    Connector.connect(src1, 0, reset, 1);
    Pullable p = reset.getPullableOutput();
    assertEquals(1f, p.pull());
    assertEquals(9f, p.pull());
    // Duplicate processor and re-pipe the queues into it
    ResetLast reset_dup = reset.duplicate(true);
    Connector.connect(src2, 0, reset_dup, 0);
    Connector.connect(src1, 0, reset_dup, 1);
    Pullable p_dup = reset_dup.getPullableOutput();
    assertEquals(18f, p_dup.pull());
    assertFalse(p_dup.hasNext());
  }
}
