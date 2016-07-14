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
package ca.uqac.lif.cep.signal;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.epl.QueueSource;

/**
 * Unit tests for the signal processing processors (!)
 * @author Sylvain Hallé
 */
public class SignalTest extends BeepBeepUnitTest
{
	@Test
	public void testPeakFinder1() throws ConnectorException
	{
		QueueSource qs = new QueueSource(null, 1);
		Vector<Object> values = new Vector<Object>();
		values.add(1);
		values.add(11); // Peak
		values.add(1);
		values.add(1);
		values.add(2); // Peak
		values.add(1);
		values.add(1);
		qs.setEvents(values);
		PeakFinderLocalMaximum pf = new PeakFinderLocalMaximum();
		Connector.connect(qs,  pf);
		Pullable p = pf.getPullableOutput(0);
		Number n;
		for (int i = 0; i < 6; i++)
		{
			n = (Number) p.pull();
			assertNull(n);			
		}
		n = (Number) p.pull();
		assertEquals(0, n.doubleValue(), 0.01); // First event is not a peak
		n = (Number) p.pull();
		assertEquals(10, n.doubleValue(), 0.01); // Second event is a peak of 10
		n = (Number) p.pull();
		assertNull(n); // Not enough info yet to conclude on 3rd event
	}
	
	@Test
	public void testPeakFinder2() throws ConnectorException
	{
		QueueSource qs = new QueueSource(null, 1);
		Vector<Object> values = new Vector<Object>();
		values.add(1);
		values.add(11); // Peak
		values.add(1);
		values.add(1);
		values.add(3); // Peak
		values.add(1);
		values.add(1);
		values.add(2);
		values.add(3);
		values.add(3);
		qs.setEvents(values);
		PeakFinderLocalMaximum pf = new PeakFinderLocalMaximum();
		Connector.connect(qs,  pf);
		Pullable p = pf.getPullableOutput(0);
		Number n;
		n = (Number) p.pullHard();
		assertEquals(0, n.doubleValue(), 0.01);
		n = (Number) p.pullHard();
		assertEquals(10, n.doubleValue(), 0.01);
		n = (Number) p.pullHard();
		assertEquals(0, n.doubleValue(), 0.01);
		n = (Number) p.pullHard();
		assertEquals(0, n.doubleValue(), 0.01);
		n = (Number) p.pullHard();
		assertEquals(2, n.doubleValue(), 0.01);
	}

	
	@Test
	public void testPlateauFinder1() throws ConnectorException
	{
		QueueSource qs = new QueueSource(null, 1);
		Vector<Object> values = new Vector<Object>();
		values.add(1);
		values.add(11);
		values.add(1);
		values.add(1);
		values.add(2);
		values.add(1);
		values.add(1); // Plateau of width 5
		values.add(4);
		qs.setEvents(values);
		PlateauFinder pf = new PlateauFinder();
		Connector.connect(qs,  pf);
		Pullable p = pf.getPullableOutput(0);
		Number n;
		for (int i = 0; i < 4; i++)
		{
			n = (Number) p.pull();
			assertNull(n);
		}
		n = (Number) p.pull(); // First event not start of a plateau
		assertEquals(0, n.floatValue(), 0.01);
		n = (Number) p.pull(); // 2nd event not start of a plateau
		assertEquals(0, n.floatValue(), 0.01);
		n = (Number) p.pull(); // 3rd is
		assertEquals(1.5, n.floatValue(), 0.01);
		n = (Number) p.pull(); // Don't create new event for the same plateau
		assertEquals(0, n.floatValue(), 0.01);
	}

}
