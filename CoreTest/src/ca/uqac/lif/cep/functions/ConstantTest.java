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
package ca.uqac.lif.cep.functions;

import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;

/**
 * Unit tests for {@link Constant}
 * 
 * @author Sylvain Hallé
 */
public class ConstantTest
{
	protected Interpreter m_interpreter;
	
	@Before
	public void setup()
	{
		m_interpreter = new Interpreter();
	}
	
	@Test
	public void testConstantGrammar1() throws ParseException
	{
		Processor proc = (Processor) m_interpreter.parseQuery("CONSTANT (0)");
		Pullable p = proc.getPullableOutput();
		Object o = p.pull();
		assertNotNull(o);
		assertTrue(o instanceof Number);
		assertEquals(0, ((Number) o).intValue());
	}
}
