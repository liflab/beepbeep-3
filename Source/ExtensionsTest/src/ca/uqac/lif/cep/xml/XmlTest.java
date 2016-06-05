package ca.uqac.lif.cep.xml;

import static org.junit.Assert.*;

import java.util.Collection;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.epl.SinkLast;
import ca.uqac.lif.xml.XPathExpression;
import ca.uqac.lif.xml.XPathExpression.XPathParseException;
import ca.uqac.lif.xml.XmlElement;
import ca.uqac.lif.xml.XmlElement.XmlParseException;

public class XmlTest 
{

	@Test
	public void testSingle1()
	{
		XmlFeeder feeder = new XmlFeeder();
		Pushable in = feeder.getPushableInput(0);
		assertNotNull(in);
		SinkLast sink = new SinkLast(1);
		Connector.connect(feeder, sink);
		in.push("<a>123</a>");
		Object[] os = sink.getLast();
		assertNotNull(os);
		assertEquals(1, os.length);
		assertTrue(os[0] instanceof XmlElement);
	}
	
	@Test
	public void testSingle2()
	{
		XmlFeeder feeder = new XmlFeeder();
		Pushable in = feeder.getPushableInput(0);
		assertNotNull(in);
		SinkLast sink = new SinkLast(1);
		Connector.connect(feeder, sink);
		in.push("<a>123</a><b></b>");
		Object[] os = sink.getLast();
		assertNull(os);
	}
	
	@Test
	public void testXPath1() throws XPathParseException, XmlParseException
	{
		XPathEvaluator xpath = new XPathEvaluator(XPathExpression.parse("a/b/text()"));
		Pushable in = xpath.getPushableInput(0);
		assertNotNull(in);
		SinkLast sink = new SinkLast(1);
		Connector.connect(xpath, sink);
		in.push(XmlElement.parse("<a><b>1</b><b>2</b></a>"));
		Object[] os = sink.getLast();
		assertNotNull(os);
		assertTrue(os[0] instanceof Collection<?>);
	}

}
