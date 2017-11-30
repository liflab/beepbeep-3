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
package ca.uqac.lif.cep.util;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.junit.Test;

import static ca.uqac.lif.cep.functions.FunctionsTest.evaluate;
import static org.junit.Assert.*;

import ca.uqac.lif.cep.functions.InvalidArgumentException;
import ca.uqac.lif.cep.numbers.AbsoluteValue;

/**
 * Unit tests for functions and processors of the <tt>util</tt> package.
 */
public class UtilTest 
{
	@SuppressWarnings("unchecked")
	@Test
	public void testApplyToAll1()
	{
		Set<Float> set = new HashSet<Float>();
		set.add(0f);
		set.add(-3f);
		set.add(5f);
		ApplyToAll ata = new ApplyToAll(AbsoluteValue.instance);
		Set<Object> out = (Set<Object>) evaluate(ata, set);
		assertEquals(3, out.size());
		assertTrue(out.contains(0f));
		assertTrue(out.contains(3f));
		assertTrue(out.contains(5f));
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testApplyToAll2()
	{
		List<Float> set = new LinkedList<Float>();
		set.add(0f);
		set.add(-3f);
		set.add(5f);
		ApplyToAll ata = new ApplyToAll(AbsoluteValue.instance);
		List<Object> out = (List<Object>) evaluate(ata, set);
		assertEquals(3, out.size());
		assertEquals(0f, out.get(0));
		assertEquals(3f, out.get(1));
		assertEquals(5f, out.get(2));
	}
	
	@Test
	public void testApplyToAll3()
	{
		Float[] set = new Float[]{0f, -3f, 5f};
		ApplyToAll ata = new ApplyToAll(AbsoluteValue.instance);
		Object[] out = (Object[]) evaluate(ata, new Object[]{set});
		assertEquals(3, out.length);
		assertEquals(0f, out[0]);
		assertEquals(3f, out[1]);
		assertEquals(5f, out[2]);
	}
	
	@Test(expected=InvalidArgumentException.class)
	public void testApplyToAll4()
	{
		ApplyToAll ata = new ApplyToAll(AbsoluteValue.instance);
		evaluate(ata, new Object());
	}
	
	@Test
	public void testNthElement1()
	{
		List<Float> set = new LinkedList<Float>();
		set.add(0f);
		set.add(-3f);
		set.add(5f);
		NthElement ata = new NthElement(1);
		float out = (Float) evaluate(ata, set);
		assertEquals(-3f, out, 0.01f);
	}
	
	@Test
	public void testNthElement2()
	{
		Float[] set = new Float[]{0f, -3f, 5f};
		NthElement ata = new NthElement(1);
		float out = (Float) evaluate(ata, new Object[]{set});
		assertEquals(-3f, out, 0.01f);
	}
	
	@Test(expected=InvalidArgumentException.class)
	public void testNthElement3()
	{
		List<Float> set = new LinkedList<Float>();
		set.add(0f);
		set.add(-3f);
		set.add(5f);
		NthElement ata = new NthElement(4);
		float out = (Float) evaluate(ata, set);
		assertEquals(-3f, out, 0.01f);
	}
	
	@Test(expected=InvalidArgumentException.class)
	public void testNthElement4()
	{
		Float[] set = new Float[]{0f, -3f, 5f};
		NthElement ata = new NthElement(4);
		float out = (Float) evaluate(ata, new Object[]{set});
		assertEquals(-3f, out, 0.01f);
	}
	
	@Test(expected=InvalidArgumentException.class)
	public void testNthElement5()
	{
		NthElement ata = new NthElement(0);
		evaluate(ata, new Object());
	}
}
