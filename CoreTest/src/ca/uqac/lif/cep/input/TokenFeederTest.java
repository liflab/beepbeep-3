package ca.uqac.lif.cep.input;

import static org.junit.Assert.assertEquals;

import java.util.Queue;
import java.util.Vector;

import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for the {@link TokenFeeder} class 
 * @author Sylvain Hallé
 */
public class TokenFeederTest extends BeepBeepUnitTest 
{
	@Test
	public void testTokenFeederPush1() throws ConnectorException
	{
		String s;
		MyFeeder mf = new MyFeeder("|", ".");
		QueueSink qsink = new QueueSink(1);
		Queue<Object> queue = qsink.getQueue(0);
		Connector.connect(mf, qsink);
		Pushable in = mf.getPushableInput(0);
		in.push("|hello.|hi.");
		assertEquals(2, queue.size());
		s = (String) queue.remove();
		assertEquals("|hello.", s);
		s = (String) queue.remove();
		assertEquals("|hi.", s);
	}
	
	@Test
	public void testTokenFeederPush2() throws ConnectorException
	{
		String s;
		MyFeeder mf = new MyFeeder("|", ".");
		QueueSink qsink = new QueueSink(1);
		Queue<Object> queue = qsink.getQueue(0);
		Connector.connect(mf, qsink);
		Pushable in = mf.getPushableInput(0);
		in.push("abc|hello.|hi.");
		assertEquals(2, queue.size());
		s = (String) queue.remove();
		assertEquals("|hello.", s);
		s = (String) queue.remove();
		assertEquals("|hi.", s);
	}
	
	@Test
	public void testTokenFeederPush3() throws ConnectorException
	{
		String s;
		MyFeeder mf = new MyFeeder("", "\n");
		QueueSink qsink = new QueueSink(1);
		Queue<Object> queue = qsink.getQueue(0);
		Connector.connect(mf, qsink);
		Pushable in = mf.getPushableInput(0);
		in.push("hello\nhi\n");
		assertEquals(2, queue.size());
		s = (String) queue.remove();
		assertEquals("hello\n", s);
		s = (String) queue.remove();
		assertEquals("hi\n", s);
	}
	
	@Test
	public void testTokenFeederPull1() throws ConnectorException
	{
		Object o;
		QueueSource qsource = new QueueSource(null, 1);
		Vector<Object> events = new Vector<Object>();
		events.add("|hello.|hi.");
		qsource.setEvents(events);
		MyFeeder mf = new MyFeeder("|", ".");
		Connector.connect(qsource, mf);
		Pullable p = mf.getPullableOutput(0);
		o = p.pull();
		assertEquals("|hello.", (String) o);
		o = p.pull();
		assertEquals("|hi.", (String) o);
	}
	
	public static class MyFeeder extends TokenFeeder
	{
		public MyFeeder(String sep_beg, String sep_end)
		{
			super();
			setSeparatorBegin(sep_beg);
			setSeparatorEnd(sep_end);
		}

		@Override
		protected Object createTokenFromInput(String token) 
		{
			return token;
		}

		@Override
		public Processor clone() 
		{
			return new MyFeeder(m_separatorBegin, m_separatorEnd);
		}
		
	}
}
