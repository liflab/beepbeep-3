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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import org.junit.Test;

import static ca.uqac.lif.cep.functions.FunctionsTest.evaluate;
import static org.junit.Assert.*;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.Cumulate;
import ca.uqac.lif.cep.functions.FunctionsTest;
import ca.uqac.lif.cep.functions.InvalidArgumentException;
import ca.uqac.lif.cep.util.Numbers;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.util.Bags.ApplyToAll;
import ca.uqac.lif.cep.util.Bags.ToArray;
import ca.uqac.lif.cep.util.Bags.ToList;
import ca.uqac.lif.cep.util.Bags.ToSet;

/**
 * Unit tests for functions and processors of the <tt>util</tt> package.
 */
public class UtilTest 
{
	@Test
	public void testContains()
	{
		Set<String> set = new HashSet<String>();
		set.add("foo");
		set.add("bar");
		set.add("baz");
		assertTrue((Boolean) evaluate(Bags.contains, set, "foo"));
		assertFalse((Boolean) evaluate(Bags.contains, set, "arf"));
	}
	
	@Test
	public void testRunOn()
	{
		Set<Integer> s = new HashSet<Integer>();
		Cumulate max = new Cumulate(new CumulativeFunction<Number>(Numbers.maximum));
		Bags.RunOn ro = new Bags.RunOn(max);
		QueueSink sink = new QueueSink();
		Queue<Object> q = sink.getQueue();
		Connector.connect(ro, sink);
		Pushable p = ro.getPushableInput();
		s.add(0);
		s.add(6);
		s.add(0);
		p.push(s);
		assertEquals(6, ((Number) q.poll()).intValue());
		s.clear();
		s.add(100);
		s.add(-1);
		s.add(3);
		s.add(72);
		p.push(s);
		assertEquals(100, ((Number) q.poll()).intValue());
		Bags.RunOn ro2 = ro.duplicate();
		assertFalse(ro == ro2);
		Connector.connect(ro2, sink);
		p = ro2.getPushableInput();
		s.clear();
		s.add(0);
		s.add(6);
		s.add(0);
		p.push(s);
		assertEquals(6, ((Number) q.poll()).intValue());
		s.clear();
		s.add(100);
		s.add(-1);
		s.add(3);
		s.add(72);
		p.push(s);
		assertEquals(100, ((Number) q.poll()).intValue());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testApplyToAll1()
	{
		Set<Float> set = new HashSet<Float>();
		set.add(0f);
		set.add(-3f);
		set.add(5f);
		ApplyToAll ata = new ApplyToAll(Numbers.absoluteValue);
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
		ApplyToAll ata = new ApplyToAll(Numbers.absoluteValue);
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
		ApplyToAll ata = new ApplyToAll(Numbers.absoluteValue);
		Object[] out = (Object[]) evaluate(ata, new Object[]{set});
		assertEquals(3, out.length);
		assertEquals(0f, out[0]);
		assertEquals(3f, out[1]);
		assertEquals(5f, out[2]);
	}
	
	@Test(expected=InvalidArgumentException.class)
	public void testApplyToAll4()
	{
		ApplyToAll ata = new ApplyToAll(Numbers.absoluteValue);
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
	
	@Test
	public void testToArray()
	{
		ToArray f = new ToArray(Number.class, String.class);
		Object[] out = (Object[]) FunctionsTest.evaluate(f, 0, "foo");
		assertEquals(2, out.length);
		assertEquals(0, out[0]);
		assertEquals("foo", out[1]);
		assertEquals(new Object[]{}.getClass(), f.getOutputTypeFor(0));
		Set<Class<?>> in_types = new HashSet<Class<?>>();
		f.getInputTypesFor(in_types, 0);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(Number.class));
		in_types.clear();
		f.getInputTypesFor(in_types, 1);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(String.class));
		ToArray f2 = f.duplicate();
		out = (Object[]) FunctionsTest.evaluate(f2, 0, "foo");
		assertEquals(2, out.length);
		assertEquals(0, out[0]);
		assertEquals("foo", out[1]);
		assertEquals(new Object[]{}.getClass(), f2.getOutputTypeFor(0));
		in_types.clear();
		f2.getInputTypesFor(in_types, 0);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(Number.class));
		in_types.clear();
		f2.getInputTypesFor(in_types, 1);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(String.class));
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testToList()
	{
		ToList f = new ToList(Number.class, String.class);
		List<Object> out = (List<Object>) FunctionsTest.evaluate(f, 0, "foo");
		assertEquals(2, out.size());
		assertEquals(0, out.get(0));
		assertEquals("foo", out.get(1));
		assertEquals(List.class, f.getOutputTypeFor(0));
		Set<Class<?>> in_types = new HashSet<Class<?>>();
		f.getInputTypesFor(in_types, 0);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(Number.class));
		in_types.clear();
		f.getInputTypesFor(in_types, 1);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(String.class));
		ToList f2 = f.duplicate();
		out = (List<Object>) FunctionsTest.evaluate(f2, 0, "foo");
		assertEquals(2, out.size());
		assertEquals(0, out.get(0));
		assertEquals("foo", out.get(1));
		assertEquals(List.class, f2.getOutputTypeFor(0));
		in_types.clear();
		f2.getInputTypesFor(in_types, 0);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(Number.class));
		in_types.clear();
		f2.getInputTypesFor(in_types, 1);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(String.class));
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testToSet()
	{
		ToSet f = new ToSet(Number.class, String.class);
		Set<Object> out = (Set<Object>) FunctionsTest.evaluate(f, 0, "foo");
		assertEquals(2, out.size());
		assertTrue(out.contains(0));
		assertTrue(out.contains("foo"));
		assertEquals(Set.class, f.getOutputTypeFor(0));
		Set<Class<?>> in_types = new HashSet<Class<?>>();
		f.getInputTypesFor(in_types, 0);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(Number.class));
		in_types.clear();
		f.getInputTypesFor(in_types, 1);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(String.class));
		ToSet f2 = f.duplicate();
		out = (Set<Object>) FunctionsTest.evaluate(f2, 0, "foo");
		assertEquals(2, out.size());
		assertTrue(out.contains(0));
		assertTrue(out.contains("foo"));
		assertEquals(Set.class, f2.getOutputTypeFor(0));
		in_types.clear();
		f2.getInputTypesFor(in_types, 0);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(Number.class));
		in_types.clear();
		f2.getInputTypesFor(in_types, 1);
		assertEquals(1, in_types.size());
		assertTrue(in_types.contains(String.class));
	}
	
	@Test
	public void testSize()
	{
		assertEquals(0, FunctionsTest.evaluate(Size.instance, new Object[]{null}));
		assertEquals(3, FunctionsTest.evaluate(Size.instance, new Object[]{new Object[]{0, 1, 2}}));
		assertEquals(2, FunctionsTest.evaluate(Size.instance, new Object[]{new String[]{"foo", "bar"}}));
		assertEquals(6, FunctionsTest.evaluate(Size.instance, "foobar"));
		assertEquals(4, FunctionsTest.evaluate(Size.instance, 4.5));
		List<Object> list = new ArrayList<Object>(2);
		list.add(new Object());
		list.add(new Object());
		assertEquals(2, FunctionsTest.evaluate(Size.instance, list));
		Set<Object> set = new HashSet<Object>(2);
		set.add(new Object());
		set.add(new Object());
		assertEquals(2, FunctionsTest.evaluate(Size.instance, set));
		Map<Integer,Integer> map = new HashMap<Integer,Integer>();
		map.put(0, 0);
		map.put(1, 1);
		assertEquals(2, FunctionsTest.evaluate(Size.instance, map));
	}
	
	@Test
	public void testStrings()
	{
		assertEquals("foobar", FunctionsTest.evaluate(Strings.concat, "foo", "bar"));
		assertEquals(false, FunctionsTest.evaluate(Strings.StartsWith.instance, "foobar", "bar"));
		assertEquals(true, FunctionsTest.evaluate(Strings.StartsWith.instance, "foobar", "foo"));
		assertEquals(true, FunctionsTest.evaluate(Strings.EndsWith.instance, "foobar", "bar"));
		assertEquals(false, FunctionsTest.evaluate(Strings.EndsWith.instance, "foobar", "foo"));
		assertEquals(true, FunctionsTest.evaluate(Strings.Contains.instance, "foobar", "oba"));
		assertEquals(false, FunctionsTest.evaluate(Strings.Contains.instance, "foobar", "obo"));
		assertEquals(true, FunctionsTest.evaluate(Strings.Matches.instance, "foobar", "f.*bar"));
		assertEquals(false, FunctionsTest.evaluate(Strings.Matches.instance, "foobar", "f.*baz"));
	}
	
	@Test
	@SuppressWarnings("unchecked")
	public void testMaps1()
	{
		Map<String,Integer> map = new HashMap<String,Integer>();
		map.put("a", 2);
		map.put("b", 3);
		map.put("c", 3);		
		Collection<Object> values = (Collection<Object>) FunctionsTest.evaluate(Maps.Values.instance, map);
		assertEquals(3, values.size());
		assertTrue(values.contains(2));
		assertTrue(values.contains(3));
	}
	
	@Test
	@SuppressWarnings("unchecked")
	public void testMapsPut1()
	{
		Map<Object,Object> m1, m2;
		QueueSource s1 = new QueueSource().setEvents(0, 1);
		QueueSource s2 = new QueueSource().setEvents(0, 1);
		Maps.PutInto pi = new Maps.PutInto();
		assertEquals(Map.class, pi.getOutputType(0));
		Connector.connect(s1, 0, pi, 0);
		Connector.connect(s2, 0, pi, 1);
		Pullable p = pi.getPullableOutput();
		m1 = (Map<Object,Object>) p.pull();
		assertEquals(1, m1.size());
		m2 = (Map<Object,Object>) p.pull();
		assertTrue(m1 == m2);
		assertEquals(2, m1.size());
		pi.reset();
		assertEquals(0, m1.size());
	}
	
	@Test
	@SuppressWarnings("unchecked")
	public void testMapsPut2()
	{
		Map<Object,Object> m1, m2;
		QueueSource s1 = new QueueSource().setEvents(new Object[]{0, 0}, new Object[]{1, 1});
		Maps.ArrayPutInto pi = new Maps.ArrayPutInto();
		assertEquals(Map.class, pi.getOutputType(0));
		Connector.connect(s1, pi);
		Pullable p = pi.getPullableOutput();
		m1 = (Map<Object,Object>) p.pull();
		assertEquals(1, m1.size());
		m2 = (Map<Object,Object>) p.pull();
		assertTrue(m1 == m2);
		assertEquals(2, m1.size());
		pi.reset();
		assertEquals(0, m1.size());
	}
	
	@Test
	@SuppressWarnings("unchecked")
	public void testSetsPut1()
	{
		Set<Object> m1, m2;
		QueueSource s1 = new QueueSource().setEvents(0, 1, 2);
		Sets.PutInto pi = new Sets.PutInto();
		assertEquals(Set.class, pi.getOutputType(0));
		Connector.connect(s1, pi);
		Pullable p = pi.getPullableOutput();
		m1 = (Set<Object>) p.pull();
		assertEquals(1, m1.size());
		m2 = (Set<Object>) p.pull();
		assertTrue(m1 == m2);
		assertEquals(2, m1.size());
		pi.reset();
		assertEquals(0, m1.size());
	}
	
	@Test
	@SuppressWarnings("unchecked")
	public void testSetsPut2()
	{
		Set<Object> m1, m2;
		QueueSource s1 = new QueueSource().setEvents(0, 1, 2);
		Sets.PutIntoNew pi = new Sets.PutIntoNew();
		assertEquals(Set.class, pi.getOutputType(0));
		Connector.connect(s1, 0, pi, 0);
		Pullable p = pi.getPullableOutput();
		m1 = (Set<Object>) p.pull();
		assertEquals(1, m1.size());
		m2 = (Set<Object>) p.pull();
		assertFalse(m1 == m2);
		assertEquals(2, m2.size());
		pi.reset();
		assertEquals(1, m1.size());
	}
	
	@Test
	public void testSubset()
	{
		Set<Integer> s1 = new HashSet<Integer>();
		s1.add(0);
		s1.add(1);
		Set<Integer> s2 = new HashSet<Integer>();
		s2.add(0);
		s2.add(1);
		s2.add(2);
		assertTrue((Boolean) FunctionsTest.evaluate(Sets.isSubsetOrEqual, s1, s2));
		s1.add(3);
		assertFalse((Boolean) FunctionsTest.evaluate(Sets.isSubsetOrEqual, s1, s2));
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testGetElementsSet()
	{
		Bags.FilterElements gi = new Bags.FilterElements(Numbers.isEven);
		Set<Integer> s1 = new HashSet<Integer>();
		s1.add(0);
		s1.add(1);
		s1.add(2);
		Set<Object> value = (Set<Object>) FunctionsTest.evaluate(gi, s1);
		assertEquals(2, value.size());
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testGetElementsList()
	{
		Bags.FilterElements gi = new Bags.FilterElements(Numbers.isEven);
		List<Integer> s1 = new ArrayList<Integer>();
		s1.add(0);
		s1.add(1);
		s1.add(2);
		List<Object> value = (List<Object>) FunctionsTest.evaluate(gi, s1);
		assertEquals(2, value.size());
		assertEquals(0, value.get(0));
		assertEquals(2, value.get(1));
	}
	
	@Test(expected=InvalidArgumentException.class)
	public void testGetElementsException()
	{
		Bags.FilterElements gi = new Bags.FilterElements(Numbers.isEven);
		FunctionsTest.evaluate(gi, new Object());
	}
}
