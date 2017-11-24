package ca.uqac.lif.cep;

import static org.junit.Assert.assertEquals;

import java.net.ConnectException;
import java.util.Arrays;
import java.util.Queue;

import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSink;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Sink;

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
		pushable.push(1);
		pushable.push(2);
		pushable.push(3);
		pushable.notifyEndOfTrace();
		
		Queue<Object> queue = sink.getQueue(0);
		assertEquals(1, (int) queue.remove());
		assertEquals(2, (int) queue.remove());
		assertEquals(3, (int) queue.remove());
		assertEquals(END_OF_TRACE, (String) queue.remove());

		
	}

}
