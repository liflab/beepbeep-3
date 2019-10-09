package ca.uqac.lif.cep;

import static ca.uqac.lif.cep.ProcessorTest.assertConnectedTo;
import static org.junit.Assert.assertEquals;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import org.junit.Test;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.azrael.clone.IdentityPrintHandler;
import ca.uqac.lif.azrael.clone.IdentityReadHandler;
import ca.uqac.lif.azrael.clone.ReadableReadHandler;
import ca.uqac.lif.cep.GroupProcessor.InputProxyConnection;
import ca.uqac.lif.cep.GroupProcessor.OutputProxyConnection;
import ca.uqac.lif.cep.GroupProcessor.ProcessorConnection;
import ca.uqac.lif.cep.Processor.NthEvent;
import ca.uqac.lif.cep.functions.SlidableFunction;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.cep.tmf.Passthrough.PassthroughQueryable;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.LabeledEdge.Quality;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthInput;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;

public class TestUtilities 
{
	/**
	 * A wrapper around {@link GroupProcessor} that exposes more of its
	 * internal member fields, for testing purposes.
	 */
	protected static class TestableGroupProcessor extends GroupProcessor
	{
		protected Map<Processor,Processor> m_correspondences;

		protected List<Processor> m_procList;

		public TestableGroupProcessor(int in_arity, int out_arity) 
		{
			super(in_arity, out_arity);
		}

		@Test
		public void test()
		{

		}

		Set<Processor> getProcessors()
		{
			return m_innerProcessors;
		}

		List<Processor> getProcessorList()
		{
			return m_procList;
		}

		Context getContextMap()
		{
			return m_context;
		}

		@Override
		public TestableGroupProcessor duplicate(boolean with_state)
		{
			TestableGroupProcessor gpw = new TestableGroupProcessor(getInputArity(), getOutputArity());
			m_correspondences = new HashMap<Processor,Processor>();
			return (TestableGroupProcessor) super.copyInto(gpw, with_state, m_correspondences);
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException
		{
			m_procList = new ArrayList<Processor>(m_innerProcessors.size());
			return print(printer, m_procList);
		}

		@Override
		protected TestableGroupProcessor getInstance(int in_arity, int out_arity)
		{
			return new TestableGroupProcessor(in_arity, out_arity);
		}		
	}

	/**
	 * A processor that provides additional public methods to expose the
	 * internal fields of the {@link SingleProcessor} class. This is used in
	 * unit tests to control the behaviour of the class under various
	 * circumstances.
	 */
	public static class TestableSingleProcessor extends SingleProcessor
	{
		protected boolean m_computeReturn = true;

		protected Queue<Object[]> m_fronts;

		protected int m_callsToEnd = 0;

		protected int m_callsToStart = 0;

		protected int m_callsToStop = 0;

		protected int m_callsToReset = 0;

		protected int m_stutterAmount = 1;

		protected Class<?> m_inputType = Object.class;

		protected Class<?> m_outputType = Object.class;

		protected Object m_state = null;

		public TestableSingleProcessor(int in_arity, int out_arity)
		{
			super(in_arity, out_arity);
			m_fronts = new ArrayDeque<Object[]>();
			m_queryable = new ProcessorQueryable(toString(), in_arity, out_arity);
		}

		public void setState(Object o)
		{
			m_state = o;
		}

		public Object getState()
		{
			return m_state;
		}

		public void setInputType(Class<?> c)
		{
			m_inputType = c;
		}

		public void setOutputType(Class<?> c)
		{
			m_outputType = c;
		}

		@Override
		public Class<?> getInputType(int index)
		{
			return m_inputType;
		}

		@Override
		public Class<?> getOutputType(int index)
		{
			return m_outputType;
		}

		public Pullable getInputPullable(int index)
		{
			return m_inputPullables[index];
		}

		public Pushable getOutputPushable(int index)
		{
			return m_outputPushables[index];
		}

		public void setStutterAmount(int n)
		{
			m_stutterAmount = n;
		}

		public int getCallsToEnd()
		{
			return m_callsToEnd;
		}

		public int getCallsToReset()
		{
			return m_callsToReset;
		}

		public Context getContextMap()
		{
			return m_context;
		}

		public Queue<Object> getInputQueue(int index)
		{
			return m_inputQueues[index];
		}

		public Queue<Object> getOutputQueue(int index)
		{
			return m_outputQueues[index];
		}

		public Queue<Object[]> getFronts()
		{
			return m_fronts;
		}

		@Override
		public void start()
		{
			m_callsToStart++;
		}

		@Override
		public void stop()
		{
			m_callsToStop++;
		}

		@Override
		public void reset()
		{
			m_callsToReset++;
			super.reset();
		}

		@Override
		public TestableSingleProcessor duplicate(boolean with_state) 
		{
			TestableSingleProcessor spw = new TestableSingleProcessor(m_inputQueues.length, m_outputQueues.length);
			return (TestableSingleProcessor) copyInto(spw, with_state);
		}

		@Override
		public boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			for (int i = 0; i < m_stutterAmount; i++)
			{
				outputs.add(inputs);
			}
			m_fronts.add(inputs);
			return m_computeReturn;
		}

		@Override
		public void onEnd(Queue<Object[]> outputs)
		{
			m_callsToEnd++;
			// We create a special output front that can be detected
			Object[] out_front = new Object[getOutputArity()];
			for (int i = 0; i < out_front.length; i++)
			{
				out_front[i] = 999;
			}
			outputs.add(out_front);
		}

		@Override
		protected SingleProcessor readState(Object state, int in_arity, int out_arity) 
		{
			TestableSingleProcessor spw = new TestableSingleProcessor(in_arity, out_arity);
			spw.m_state = state;
			return spw;
		}

		@Override
		protected Object printState() 
		{
			return m_state;
		}

		public int getCallsToStart()
		{
			return m_callsToStart;
		}

		public int getCallsToStop()
		{
			return m_callsToStop;
		}

		@Override
		protected TestableSingleProcessorQueryable getQueryable(int in_arity, int out_arity)
		{
			return new TestableSingleProcessorQueryable(toString(), in_arity, out_arity);
		}

		public static class TestableSingleProcessorQueryable extends ProcessorQueryable
		{
			public TestableSingleProcessorQueryable(String reference, int in_arity, int out_arity) 
			{
				super(reference, in_arity, out_arity);
			}

			@Override
			protected List<TraceabilityNode> queryInput(TraceabilityQuery q, int in_index, Designator tail, TraceabilityNode root, Tracer factory)
			{
				Designator t_head = tail.peek();
				Designator t_tail = tail.tail();
				if (!(t_head instanceof NthEvent))
				{
					// Unknown
					return super.queryOutput(q, in_index, t_tail, root, factory);
				}
				NthEvent nth = (NthEvent) t_head;
				int index = nth.getIndex();
				ComposedDesignator cd = new ComposedDesignator(t_tail, new NthEvent(index), new NthOutput(in_index));
				TraceabilityNode node = factory.getObjectNode(cd, this);
				root.addChild(node, Quality.EXACT);
				List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>(1);
				leaves.add(node);
				return leaves;
			}

			@Override
			protected List<TraceabilityNode> queryOutput(TraceabilityQuery q, int out_index, Designator tail, TraceabilityNode root, Tracer factory)
			{
				Designator t_head = tail.peek();
				Designator t_tail = tail.tail();
				if (!(t_head instanceof NthEvent))
				{
					// Unknown
					return super.queryOutput(q, out_index, t_tail, root, factory);
				}
				NthEvent nth = (NthEvent) t_head;
				int index = nth.getIndex();
				ComposedDesignator cd = new ComposedDesignator(t_tail, new NthEvent(index), new NthInput(out_index));
				TraceabilityNode node = factory.getObjectNode(cd, this);
				root.addChild(node, Quality.EXACT);
				List<TraceabilityNode> leaves = new ArrayList<TraceabilityNode>(1);
				leaves.add(node);
				return leaves;
			}

			@Override
			public Object printState()
			{
				return null;
			}

			@Override
			public TestableSingleProcessorQueryable readState(/*@ non_null @*/ String reference, int in_arity, int out_arity, /*@ nullable @*/ Object state) throws ReadException
			{
				return new TestableSingleProcessorQueryable(reference, in_arity, out_arity);
			}

			@Override
			public TestableSingleProcessorQueryable duplicate(boolean with_state)
			{
				return new TestableSingleProcessorQueryable(m_reference, m_inputConnections.length, m_outputConnections.length);
			}
		}
	}

	/**
	 * A configurable {@link QueueSource} with additional methods to expose
	 * its internal state. This is used in
	 * unit tests to control the behaviour of the class under various
	 * circumstances.
	 */
	public static class StutteringQueueSource extends QueueSource
	{
		protected int m_stutterAmount = 1;

		protected int m_computeCount = 0;

		protected void setStutterAmount(int n)
		{
			m_stutterAmount = n;
		}

		protected int getComputeCount()
		{
			return m_computeCount;
		}

		@Override
		public boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			m_computeCount++;
			if (m_stutterAmount < 0)
			{
				if (m_computeCount % (-m_stutterAmount) == 0)
				{
					return super.compute(inputs, outputs);
				}
			}
			else
			{
				for (int i = 0; i < m_stutterAmount; i++)
				{
					if (!super.compute(inputs, outputs))
					{
						return false;
					}
				}
			}
			return true;
		}
	}

	public static class IdentityObjectPrinter extends ObjectPrinter<Object>
	{
		public IdentityObjectPrinter()
		{
			super();
			addHandler(new IdentityPrintHandler());
		}

		@Override
		public Object wrap(Object o, Object t) throws PrintException 
		{
			return t;
		}
	}

	public static class IdentityObjectReader extends ObjectReader<Object>
	{
		public IdentityObjectReader()
		{
			super();
			addHandler(new ReadableReadHandler(this));
			addHandler(new IdentityReadHandler());
		}

		public Object read(Object o, Readable reference) throws ReadException
		{
			return reference.read(this, o);
		}

		@Override
		protected Class<?> unwrapType(Object t) throws ReadException
		{
			return t.getClass();
		}

		@Override
		protected Object unwrapContents(Object t) throws ReadException 
		{
			return t;
		}

		@Override
		protected boolean isWrapped(Object t) 
		{
			return false;
		}
	}

	public static class TestableQueueSource extends QueueSource
	{
		protected int m_callsToCompute = 0;

		@Override
		public boolean compute(Object[] inputs, Queue<Object[]> outputs)
		{
			m_callsToCompute++;
			return super.compute(inputs, outputs);
		}
	}

	/**
	 * A {@link SlidableFunction} with additional methods to query its internal
	 * state, for testing purposes.
	 */
	public static class TestableSlidableFunction implements SlidableFunction
	{
		protected List<Object> m_buffer;

		protected int m_callsToEvaluate = 0;

		protected int m_callsToDevaluate = 0;

		protected int m_callsToReset = 0;

		protected Object m_lastEvaluate;

		protected Object m_lastDevaluate;

		public TestableSlidableFunction()
		{
			super();
			m_buffer = new ArrayList<Object>();
		}

		public Object getLastEvaluate()
		{
			return m_lastEvaluate;
		}

		public Object getLastDevaluate()
		{
			return m_lastDevaluate;
		}

		@Override
		public int getInputArity() 
		{
			return 1;
		}

		@Override
		public int getOutputArity() 
		{
			return 1;
		}

		public int getCallsToEvaluate()
		{
			return m_callsToEvaluate;
		}

		public int getCallsToDevaluate()
		{
			return m_callsToDevaluate;
		}

		public int getCallsToReset()
		{
			return m_callsToReset;
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs) 
		{
			m_buffer.add(inputs[0]);
			m_callsToEvaluate++;
			m_lastEvaluate = inputs[0];
		}

		@Override
		public void evaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_buffer.add(inputs[0]);
			m_callsToEvaluate++;
			m_lastEvaluate = inputs[0];
		}

		@Override
		public void reset() 
		{
			m_buffer.clear();
			m_callsToReset++;
			m_lastEvaluate = null;
			m_lastDevaluate = null;
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException
		{
			return m_buffer;
		}

		@SuppressWarnings("unchecked")
		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException 
		{
			TestableSlidableFunction tsf = new TestableSlidableFunction();
			tsf.m_buffer = (List<Object>) reader.read(o);
			return tsf;
		}

		@Override
		public TestableSlidableFunction duplicate(boolean with_state)
		{
			TestableSlidableFunction tsf = new TestableSlidableFunction();
			if (with_state)
			{
				tsf.m_buffer.addAll(m_buffer);
			}
			return tsf;
		}

		@Override
		public TestableSlidableFunction duplicate() 
		{
			return duplicate(false);
		}

		@Override
		public void devaluate(Object[] inputs, Object[] outputs, Context context) 
		{
			m_lastDevaluate = inputs[0];
			m_callsToDevaluate++;
		}

		@Override
		public void devaluate(Object[] inputs, Object[] outputs) 
		{
			m_lastDevaluate = inputs[0];
			m_callsToDevaluate++;
		}
	}

	/**
	 * Checks that the connections listed in the <tt>connections</tt> element
	 * of the serialized group match the actual connections between the
	 * processors in the group.
	 * @param gp The group that has been serialized
	 * @param proc_list The list of processors in the group, at the same positions
	 * as the ones in the serialized list of processors
	 * @param connections The list of serialized connections to verify
	 */
	public static void verifyConnections(GroupProcessor gp, List<Processor> proc_list, List<ProcessorConnection> connections)
	{
		for (ProcessorConnection pc : connections)
		{
			if (pc.m_sourceId == -1)
			{
				InputProxyConnection ipc = gp.m_inputPlaceholders[pc.m_sourceIndex];
				assertEquals(ipc.m_pushable.getIndex(), pc.m_destinationIndex);
				assertEquals(ipc.m_pushable.getObject(), proc_list.get(pc.m_destinationId));
			}
			else if (pc.m_destinationId == -1)
			{
				OutputProxyConnection opc = gp.m_outputPlaceholders[pc.m_destinationIndex];
				assertEquals(opc.m_pullable.getIndex(), pc.m_sourceIndex);
				assertEquals(opc.m_pullable.getObject(), proc_list.get(pc.m_sourceId));
			}
			else
			{
				Processor p1 = proc_list.get(pc.m_sourceId);
				Processor p2 = proc_list.get(pc.m_destinationId);
				assertConnectedTo(p1, pc.m_sourceIndex, p2, pc.m_destinationIndex);
			}
		}
	}
}
