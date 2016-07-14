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
package ca.uqac.lif.cep.json;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.epl.SinkLast;
import ca.uqac.lif.json.JsonList;
import ca.uqac.lif.json.JsonMap;
import ca.uqac.lif.json.JsonParser;
import ca.uqac.lif.json.JsonParser.JsonParseException;

/**
 * Unit tests for the {@link JsonFeeder} and {@link JPathEvaluator}
 * @author Sylvain Hallé
 */
public class JsonTest extends BeepBeepUnitTest 
{
	protected static JsonParser s_parser = new JsonParser();
	
	@Test
	public void testSingle1() throws ConnectorException
	{
		JsonFeeder feeder = new JsonFeeder();
		Pushable in = feeder.getPushableInput(0);
		assertNotNull(in);
		SinkLast sink = new SinkLast(1);
		Connector.connect(feeder, sink);
		in.push("{\"a\" : 123}");
		Object[] os = sink.getLast();
		assertNotNull(os);
		assertEquals(1, os.length);
		assertTrue(os[0] instanceof JsonMap);
	}
	
	@Test
	public void testSingle2() throws ConnectorException
	{
		JsonFeeder feeder = new JsonFeeder();
		Pushable in = feeder.getPushableInput(0);
		assertNotNull(in);
		SinkLast sink = new SinkLast(1);
		Connector.connect(feeder, sink);
		in.push("{\"a\" : 123}b");
		Object[] os = sink.getLast();
		assertNull(os);
	}
	
	@Test
	public void testJPath1() throws JsonParseException, ConnectorException
	{
		JPathEvaluator jpath = new JPathEvaluator("a.b");
		Pushable in = jpath.getPushableInput(0);
		assertNotNull(in);
		SinkLast sink = new SinkLast(1);
		Connector.connect(jpath, sink);
		in.push(s_parser.parse("{\"a\" : { \"b\" : [1,2]}}"));
		Object[] os = sink.getLast();
		assertNotNull(os);
		assertTrue(os[0] instanceof JsonList);
	}
}
