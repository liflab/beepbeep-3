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
package ca.uqac.lif.cep.fsm;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.epl.QueueSource;
import ca.uqac.lif.cep.tuples.AttributePlaceholder;
import ca.uqac.lif.cep.tuples.EqualsExpression;
import ca.uqac.lif.cep.tuples.NumberExpression;
import ca.uqac.lif.cep.tuples.Select;

/**
 * Unit tests for the Moore Machine processor
 */
public class MooreTest extends BeepBeepUnitTest
{
	// State names; this is just to improve readability
	public static final int ST_0 = 0;
	public static final int ST_1 = 1;
	public static final int ST_2 = 2;
	public static final int ST_3 = 3;
	
	@Test
	public void testMoore1() throws ConnectorException
	{
		// Setup event source
		QueueSource source = new QueueSource(null, 1);
		Vector<Object> events = new Vector<Object>();
		events.add(1);
		events.add(2);
		source.setEvents(events);
		// Setup Moore machine
		MooreMachine m = new MooreMachine(1, 1);
		m.addTransition(ST_0, new ProcessorTransition(ST_1,
				// in state 0, event = 2, go to state 1
				new Select(1, new EqualsExpression(new AttributePlaceholder(), new NumberExpression(2)))));
		m.addTransition(ST_0, new ProcessorTransition(ST_0,
				// in state 0, event = 1, go to state 0
				new Select(1, new EqualsExpression(new AttributePlaceholder(), new NumberExpression(1)))));
		m.addSymbol(0, "In zero");
		m.addSymbol(1, "In one");
		Connector.connect(source, m);
		Pullable p = m.getPullableOutput(0);
		Object event = null;
		event = p.pull();
		assertNotNull(event);
		assertEquals("In zero", event);
		event = p.pull();
		assertEquals("In one", event);
		
	}

}
