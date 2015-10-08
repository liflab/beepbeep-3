/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep.signal;

import static org.junit.Assert.*;

import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.QueueSource;
import ca.uqac.lif.cep.eml.tuples.EmlNumber;

public class SignalTest 
{
	@Test
	public void testPeakFinder1()
	{
		QueueSource qs = new QueueSource(null, 1);
		Vector<Object> values = new Vector<Object>();
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(11)); // Peak
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(2)); // Peak
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(1));
		qs.setEvents(values);
		PeakFinderLocalMaximum pf = new PeakFinderLocalMaximum();
		Connector.connect(qs,  pf);
		Pullable p = pf.getPullableOutput(0);
		EmlNumber n;
		for (int i = 0; i < 6; i++)
		{
			n = (EmlNumber) p.pull();
			assertNull(n);			
		}
		n = (EmlNumber) p.pull();
		assertEquals(0, n.doubleValue(), 0.01); // First event is not a peak
		n = (EmlNumber) p.pull();
		assertEquals(10, n.doubleValue(), 0.01); // Second event is a peak of 10
		n = (EmlNumber) p.pull();
		assertNull(n); // Not enough info yet to conclude on 3rd event
	}
	
	@Test
	public void testPeakFinder2()
	{
		QueueSource qs = new QueueSource(null, 1);
		Vector<Object> values = new Vector<Object>();
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(11)); // Peak
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(3)); // Peak
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(2));
		values.add(new EmlNumber(3));
		values.add(new EmlNumber(3));
		qs.setEvents(values);
		PeakFinderLocalMaximum pf = new PeakFinderLocalMaximum();
		Connector.connect(qs,  pf);
		Pullable p = pf.getPullableOutput(0);
		EmlNumber n;
		n = (EmlNumber) p.pullHard();
		assertEquals(0, n.doubleValue(), 0.01);
		n = (EmlNumber) p.pullHard();
		assertEquals(10, n.doubleValue(), 0.01);
		n = (EmlNumber) p.pullHard();
		assertEquals(0, n.doubleValue(), 0.01);
		n = (EmlNumber) p.pullHard();
		assertEquals(0, n.doubleValue(), 0.01);
		n = (EmlNumber) p.pullHard();
		assertEquals(2, n.doubleValue(), 0.01);
	}

	
	@Test
	public void testPlateauFinder1()
	{
		QueueSource qs = new QueueSource(null, 1);
		Vector<Object> values = new Vector<Object>();
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(11));
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(2));
		values.add(new EmlNumber(1));
		values.add(new EmlNumber(1)); // Plateau of width 5
		values.add(new EmlNumber(4));
		qs.setEvents(values);
		PlateauFinder pf = new PlateauFinder();
		Connector.connect(qs,  pf);
		Pullable p = pf.getPullableOutput(0);
		EmlNumber n;
		for (int i = 0; i < 4; i++)
		{
			n = (EmlNumber) p.pull();
			assertNull(n);
		}
		n = (EmlNumber) p.pull(); // First event not start of a plateau
		assertEquals(0, n.doubleValue(), 0.01);
		n = (EmlNumber) p.pull(); // 2nd event not start of a plateau
		assertEquals(0, n.doubleValue(), 0.01);
		n = (EmlNumber) p.pull(); // 3rd is
		assertEquals(1.5, n.doubleValue(), 0.01);
		n = (EmlNumber) p.pull(); // Don't create new event for the same plateau
		assertEquals(0, n.doubleValue(), 0.01);
	}

}
