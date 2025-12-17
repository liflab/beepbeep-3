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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.clone.ClonePrinter;
import ca.uqac.lif.azrael.clone.CloneReader;
import ca.uqac.lif.cep.Processor.InternalProcessorState;
import ca.uqac.lif.cep.tmf.Passthrough;
import org.junit.Test;

/**
 * Unit tests for the {@link Passthrough} processor.
 * @author Sylvain Hallé
 */
public class PassthroughTest
{
  @Test
  public void testPassthrough1() throws ProcessorException, PrintException, ReadException
  {
    ClonePrinter printer = new ClonePrinter();
    CloneReader reader = new CloneReader();
    Passthrough proc = new Passthrough();
    Object e = printer.print(proc);
    assertNotNull(e);
    Object o = reader.read(e);
    assertNotNull(o);
    assertTrue(o instanceof Passthrough);
    Passthrough proc2 = (Passthrough) o;
    assertFalse(proc == proc2);
  }
  
	@Test
	public void testInternalState1()
	{
		Passthrough p1 = new Passthrough();
		Passthrough p2 = new Passthrough();
		InternalProcessorState s1 = new InternalProcessorState(p1);
		InternalProcessorState s2 = new InternalProcessorState(p2);
		assertEquals(s1, s2);
	}
}
