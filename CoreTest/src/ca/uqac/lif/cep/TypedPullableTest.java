/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for the {@link TypedPullable} class.
 */
public class TypedPullableTest 
{
	@Test
	public void testTypedPullable1() 
	{
		QueueSource qs = new QueueSource(1);
		qs.addEvent("A");
		Passthrough pt = new Passthrough(1);
		Connector.connect(qs, pt);
		Pullable p = pt.getPullableOutput(0);
		TypedPullable<String> tp = new TypedPullable<String>(p);
		assertEquals(Pullable.NextStatus.YES, tp.hasNextSoft());
		String s = tp.pullSoft();
		assertEquals("A", s);
		assertEquals(pt.getId(), tp.getProcessor().getId());
		assertEquals(0, tp.getPosition());
	}

	@Test
	public void testTypedPullable2() 
	{
		QueueSource qs = new QueueSource(1);
		qs.addEvent("A");
		Passthrough pt = new Passthrough(1);
		Connector.connect(qs, pt);
		Pullable p = pt.getPullableOutput(0);
		TypedPullable<String> tp = new TypedPullable<String>(p);
		assertTrue(tp.hasNext());
		String s = tp.pull();
		assertEquals("A", s);
		// These should do nothing
		tp.start();
		tp.stop();
		tp.dispose();
		int cnt = 0;
		try
		{
			tp.remove();
		}
		catch (UnsupportedOperationException e)
		{
			cnt++;
		}
		assertEquals(1, cnt);
	}
	
	@SuppressWarnings("unused")
	@Test
	public void testTypedPullable3() 
	{
		QueueSource qs = new QueueSource(1);
		qs.addEvent("A");
		Pullable p = qs.getPullableOutput(0);
		TypedPullable<Integer> tp = new TypedPullable<Integer>(p);
		int cnt = 0;
		try
		{
			Integer i = tp.pull();
		}
		catch (ClassCastException e)
		{
			cnt++;
		}
		try
		{
			Integer i = tp.pullSoft();
		}
		catch (ClassCastException e)
		{
			cnt++;
		}
		try
		{
			Integer i = tp.next();
		}
		catch (ClassCastException e)
		{
			cnt++;
		}
		assertEquals(3, cnt);
	}

}
