package ca.uqac.lif.cep;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Queue;

import ca.uqac.lif.cep.tmf.*;
import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;

import javax.swing.*;

public class EndOfTraceTest {
	
	private final static String END_OF_TRACE = "End of trace";
	
	public class EndOfTracePassthrough extends Passthrough {
		public EndOfTracePassthrough(int i) {
			super(i);
		}

		@Override
		protected boolean onEndOfTrace(Object[] outputs) throws ProcessorException {
			System.out.println(END_OF_TRACE);
			Arrays.fill(outputs, END_OF_TRACE);
			return true;
		}
	}
	
	
	@Test
	public void testEndOfTracePrinter() throws ConnectorException {
		EndOfTracePassthrough endOfTracePassthrough = new EndOfTracePassthrough(1);
		QueueSink sink = new QueueSink(1);
		
		Connector.connect(endOfTracePassthrough, sink);
		
		Pushable pushable = endOfTracePassthrough.getPushableInput(0);
		Queue<Object> queue = sink.getQueue(0);
		for(int i = 0; i < 10; i++) 
		{
			pushable.push(i);
			assertEquals(i, (int) queue.remove());
		}
		pushable.notifyEndOfTrace();
		assertEquals(END_OF_TRACE, (String) queue.remove());
	}
	
	
	@Test
	public void testMultiplexer() throws ConnectorException {
		Multiplexer multiplexer = new Multiplexer(2);
		EndOfTracePassthrough endOfTracePassthrough = new EndOfTracePassthrough(1);
		QueueSink sink = new QueueSink(1);
		
		Connector.connect(multiplexer, endOfTracePassthrough, sink);
		
		Pushable pushable0 = multiplexer.getPushableInput(0);
		Pushable pushable1 = multiplexer.getPushableInput(1);
		Queue<Object> queue = sink.getQueue(0);
		
		for(int i = 0; i < 10; i++)
		{
			if(i < 5)
				pushable0.push(i);
			else 
				pushable0.notifyEndOfTrace();
			
			pushable1.push(i+100);
			
			if(i < 5)
				assertEquals(i, (int) queue.remove());
			assertEquals(i+100, (int) queue.remove());
		}		
		pushable1.notifyEndOfTrace();
		assertEquals(END_OF_TRACE, (String) queue.remove());
	}

	
	@Test
	public void testPump() throws ConnectorException {
		QueueSource source = new QueueSource();
		Pump pump = new Pump();
		Passthrough passthrough = new EndOfTracePassthrough(1);
		QueueSink sink = new QueueSink(1);
		
		Connector.connect(source, pump, passthrough, sink);
		
		source.loop(false);
		for(int i = 0; i < 10; i++)
			source.addEvent(i);
		
		pump.run();
		
		Queue<Object> queue = sink.getQueue(0);
		for(int i = 0; i < 10; i++) 
			assertEquals(i, (int) queue.remove());
		
		assertEquals(END_OF_TRACE, (String) queue.remove());		
	}

	@Test
	public void testGroupProcessor() throws ConnectorException {
		Passthrough
				passthrough0 = new EndOfTracePassthrough(1),
				passthrough1 = new EndOfTracePassthrough(1);
		Connector.connect(passthrough0, passthrough1);

		GroupProcessor groupProcessor = new GroupProcessor(1, 1);
		groupProcessor.associateInput(0, passthrough0, 0);
		groupProcessor.associateOutput(0, passthrough1, 0);


		QueueSink sink = new QueueSink(1);
		Connector.connect(groupProcessor, sink);

		Pushable pushable = groupProcessor.getPushableInput(0);
		Queue<Object> queueSink = sink.getQueue(0);

		for(int i = 0; i < 10; i++)
		{
			pushable.push(i);
			assertEquals(i, (int) queueSink.remove());
		}

		pushable.notifyEndOfTrace();
		assertEquals(END_OF_TRACE, (String) queueSink.remove());
	}

	@Test
	public void testCountDecimate() throws ConnectorException {

		int interval = 3;

		CountDecimate countDecimate0 = new CountDecimate(interval);
		CountDecimate countDecimate1 = new CountDecimate(interval, true);

		QueueSink sink0 = new QueueSink(1);
		QueueSink sink1 = new QueueSink(1);

		Connector.connect(countDecimate0, sink0);
		Connector.connect(countDecimate1, sink1);

		Pushable pushable0 = countDecimate0.getPushableInput(0);
		Pushable pushable1 = countDecimate1.getPushableInput(0);

		Queue<Object> queueSink0 = sink0.getQueue(0);
		Queue<Object> queueSink1 = sink1.getQueue(0);

		int lastInput = 0;

		for(int i = 0; i < 9; i++)
		{
			pushable0.push(i);
			pushable1.push(i);

			if(i % interval == 0)
			{
				assertEquals(i, (int) queueSink0.remove());
				assertEquals(i, (int) queueSink1.remove());
			}

			lastInput = i;
		}

		pushable0.notifyEndOfTrace();
		assertTrue(queueSink0.isEmpty());

		pushable1.notifyEndOfTrace();
		if(lastInput % interval != 0)
		{
			assertEquals(lastInput, (int) queueSink1.remove());
		}
		assertTrue(queueSink1.isEmpty());
	}
}
