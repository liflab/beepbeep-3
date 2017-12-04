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

import static org.junit.Assert.*;

import org.junit.Test;

import ca.uqac.lif.cep.Pullable.PullableException;
import ca.uqac.lif.cep.functions.StreamVariable;
import ca.uqac.lif.cep.functions.Constant;
import ca.uqac.lif.cep.functions.ApplyFunction;
import ca.uqac.lif.cep.functions.FunctionTree;
import ca.uqac.lif.cep.util.Numbers;
import ca.uqac.lif.cep.tmf.ReplaceWith;
import ca.uqac.lif.cep.tmf.Pump;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for the {@link Pullable} interface.
 */
public class PullableTest
{
	@Test(expected=PullableException.class)
	public void testPullableException1()
	{
		ApplyFunction div = new ApplyFunction(new FunctionTree(Numbers.division, new Constant(1), new StreamVariable(0)));
		Pullable p = div.getPullableOutput();
		p.pull();
	}
	
	@Test
	public void testPullNotSupported1() 
	{
		QueueSource s = new QueueSource();
		s.setEvents(new Object[]{0});
		Pump pump = new Pump();
		Connector.connect(s, pump);
		Pullable p = pump.getPullableOutput();
		assertTrue(p instanceof Pullable.PullNotSupported);
		int cnt = 0;
		try
		{
			p.pull();
		}
		catch (UnsupportedOperationException e)
		{
			cnt++;
		}
		try
		{
			p.pullSoft();
		}
		catch (UnsupportedOperationException e)
		{
			cnt++;
		}
		try
		{
			p.hasNext();
		}
		catch (UnsupportedOperationException e)
		{
			cnt++;
		}
		try
		{
			p.next();
		}
		catch (UnsupportedOperationException e)
		{
			cnt++;
		}
		try
		{
			p.hasNextSoft();
		}
		catch (UnsupportedOperationException e)
		{
			cnt++;
		}
		try
		{
			p.remove();
		}
		catch (UnsupportedOperationException e)
		{
			cnt++;
		}
		try
		{
			p.iterator();
		}
		catch (UnsupportedOperationException e)
		{
			cnt++;
		}
		assertEquals(7, cnt);
		// These methods should do nothing
		p.dispose();
		p.start();
		p.stop();
		assertEquals(0, p.getPosition());
		assertEquals(pump.getId(), p.getProcessor().getId());
	}
	
	@Test
	@SuppressWarnings("unused")
	public void testPullableException2()
	{
		// Constructor test; we just check that it runs
		PullableException pe = new PullableException("foo");
	}
	
	@Test
	@SuppressWarnings("unused")
	public void testPullableException3()
	{
		// Constructor test; we just check that it runs
		try
		{
			// Create an exception
			int a = 0;
			int b = 4 / a;
		}
		catch (Exception e)
		{
			PullableException pe = new PullableException(e);
		}
	}
	
	@Test
	@SuppressWarnings("unused")
	public void testPullableException4()
	{
		// Constructor test; we just check that it runs
		Processor p = new ReplaceWith(Constant.ZERO);
		try
		{
			// Create an exception
			int a = 0;
			int b = 4 / a;
		}
		catch (Exception e)
		{
			PullableException pe = new PullableException(e, p);
		}
	}

}
