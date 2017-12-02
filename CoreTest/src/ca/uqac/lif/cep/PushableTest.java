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

import ca.uqac.lif.cep.Pushable.PushableException;
import ca.uqac.lif.cep.functions.StreamVariable;
import ca.uqac.lif.cep.functions.Constant;
import ca.uqac.lif.cep.functions.ApplyFunction;
import ca.uqac.lif.cep.functions.FunctionTree;
import ca.uqac.lif.cep.util.Numbers;
import ca.uqac.lif.cep.tmf.ReplaceWith;
import ca.uqac.lif.cep.tmf.Pump;

public class PushableTest
{
	@Test(expected=PushableException.class)
	public void testPushableException1()
	{
		ApplyFunction div = new ApplyFunction(new FunctionTree(Numbers.division, new Constant(1), new StreamVariable(0)));
		Pushable p = div.getPushableInput();
		p.push(0);
	}
	
	@Test
	public void testPushNotSupported1() 
	{
		Pump pump = new Pump();
		Pushable p = pump.getPushableInput();
		assertTrue(p instanceof Pushable.PushNotSupported);
		int cnt = 0;
		try
		{
			p.push(0);
		}
		catch (UnsupportedOperationException e)
		{
			cnt++;
		}
		try
		{
			p.pushFast(0);
		}
		catch (UnsupportedOperationException e)
		{
			cnt++;
		}
		assertEquals(2, cnt);
		// These methods should do nothing
		p.dispose();
		p.waitFor();
		assertEquals(0, p.getPosition());
		assertEquals(pump.getId(), p.getProcessor().getId());
	}
	
	@Test
	@SuppressWarnings("unused")
	public void testPushableException2()
	{
		// Constructor test; we just check that it runs
		PushableException pe = new PushableException("foo");
	}
	
	@Test
	@SuppressWarnings("unused")
	public void testPushableException3()
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
			PushableException pe = new PushableException(e);
		}
	}
	
	@Test
	@SuppressWarnings("unused")
	public void testPushableException4()
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
			PushableException pe = new PushableException(e, p);
		}
	}
}
