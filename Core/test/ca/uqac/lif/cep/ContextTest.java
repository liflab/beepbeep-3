package ca.uqac.lif.cep;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.junit.Test;

import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectPrinter;
import ca.uqac.lif.cep.TestUtilities.IdentityObjectReader;
import ca.uqac.lif.petitpoucet.common.Context;

public class ContextTest
{
	@Test
	public void testGet()
	{
		Context c = new Context();
		c.put("foo", "bar");
		assertEquals("bar", c.get("foo"));
		assertNull(c.get("baz"));
	}
	
	@Test
	public void testClear()
	{
		Context c = new Context();
		c.put("foo", "bar");
		c.clear();
		assertTrue(c.isEmpty());
	}
	
	@Test
	public void testKeySet()
	{
		Context c = new Context();
		c.put("foo", 0);
		c.put("bar", 1);
		c.put("baz", 2);
		Set<String> keyset = c.keySet();
		assertEquals(3, keyset.size());
		assertTrue(keyset.contains("foo"));
		assertTrue(keyset.contains("bar"));
		assertTrue(keyset.contains("baz"));
		assertTrue(c.containsKey("foo"));
		assertFalse(c.containsKey("999"));
	}
	
	@Test
	public void testRemove()
	{
		Context c = new Context();
		c.put("foo", 0);
		c.put("bar", 1);
		c.put("baz", 2);
		assertEquals(3,  c.size());
		c.remove("foo");
		assertEquals(2,  c.size());
		assertNull(c.get("foo"));
	}
	
	@Test
	public void testValues()
	{
		Context c = new Context();
		c.put("foo", 0);
		c.put("bar", 1);
		c.put("baz", 2);
		Collection<Object> values = c.values();
		assertEquals(3, values.size());
		assertTrue(values.contains(0));
		assertTrue(values.contains(1));
		assertTrue(values.contains(2));
		assertTrue(c.containsValue(0));
		assertFalse(c.containsValue(3));
	}
	
	@SuppressWarnings("unchecked")
	@Test
	public void testPrint() throws PrintException
	{
		Context c = new Context();
		c.put("foo", 0);
		c.put("bar", 1);
		IdentityObjectPrinter iop = new IdentityObjectPrinter();
		Object o = iop.print(c);
		assertTrue(o instanceof Map);
		Map<String,Object> map = (Map<String,Object>) o;
		assertEquals(2, map.size());
		assertEquals(0, map.get("foo"));
		assertEquals(1, map.get("bar"));
	}
	
	@Test
	public void testRead1() throws ReadException
	{
		Map<String,Object> map = new HashMap<String,Object>();
		map.put("foo", 1);
		map.put("bar", 2);
		IdentityObjectReader ior = new IdentityObjectReader();
		Context c = (Context) new Context().read(ior, map);
		assertEquals(2, c.size());
		assertEquals(1, c.getOrDefault("foo", null));
		assertEquals(2, c.getOrDefault("bar", null));
	}
	
	@Test(expected = ReadException.class)
	public void testReadInvalid1() throws ReadException
	{
		IdentityObjectReader ior = new IdentityObjectReader();
		new Context().read(ior, 3);
	}
}