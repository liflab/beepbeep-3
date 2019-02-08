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
package ca.uqac.lif.cep;

import static org.junit.Assert.assertEquals;

import ca.uqac.lif.cep.tmf.QueueSource;
import org.junit.Test;

/**
 * Unit tests for the {@link Doubler} class.
 * @author Sylvain Hallé
 */
public class DoublerTest
{
  @Test
  public void test1()
  {
    QueueSource src1 = new QueueSource().setEvents(3, 1, 4, 1);
    Doubler add = new Doubler();
    Connector.connect(src1, 0, add, 0);
    Pullable p = add.getPullableOutput();
    assertEquals(6, ((Integer) p.pull()).intValue());
    assertEquals(2, ((Integer) p.pull()).intValue());
    assertEquals(8, ((Integer) p.pull()).intValue());
    assertEquals(2, ((Integer) p.pull()).intValue());
  }
}