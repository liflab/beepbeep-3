/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2025 Sylvain Hallé

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

import static org.junit.Assert.*;

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
	public void testInternalState1()
	{
		Passthrough p1 = new Passthrough();
		Passthrough p2 = new Passthrough();
		InternalProcessorState s1 = new InternalProcessorState(p1);
		InternalProcessorState s2 = new InternalProcessorState(p2);
		assertEquals(s1, s2);
	}
}
