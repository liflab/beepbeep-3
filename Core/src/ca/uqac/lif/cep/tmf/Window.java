package ca.uqac.lif.cep.tmf;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Queue;

import ca.uqac.lif.azrael.ObjectPrinter;
import ca.uqac.lif.azrael.ObjectReader;
import ca.uqac.lif.azrael.PrintException;
import ca.uqac.lif.azrael.Printable;
import ca.uqac.lif.azrael.Readable;
import ca.uqac.lif.azrael.ReadException;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorQueryable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.StateDuplicable;
import ca.uqac.lif.cep.functions.SlidableFunction;
import ca.uqac.lif.cep.tmf.SinkLast.SinkContents;
import ca.uqac.lif.cep.tmf.Window.GenericWindow.WindowQueryable;
import ca.uqac.lif.petitpoucet.ComposedDesignator;
import ca.uqac.lif.petitpoucet.Designator;
import ca.uqac.lif.petitpoucet.Queryable;
import ca.uqac.lif.petitpoucet.TraceabilityNode;
import ca.uqac.lif.petitpoucet.TraceabilityQuery;
import ca.uqac.lif.petitpoucet.Tracer;
import ca.uqac.lif.petitpoucet.circuit.CircuitDesignator.NthOutput;
import ca.uqac.lif.petitpoucet.common.CollectionDesignator.NthElement;

public class Window extends SingleProcessor
{
	/*@ non_null @*/ protected GenericWindow m_windowProcessor;
	
	public static final transient String s_widthKey = "width";
	
	public static final transient String s_windowKey = "window";
	
	// requires width > 0;
	public Window(/*@ non_null @*/ Processor p, int width)
	{
		this(new ProcessorWindow(p, width));
	}

	// requires width > 0;
	public Window(/*@ non_null @*/ SlidableFunction f, int width)
	{
		this(new SlidableWindow(f, width));
	}

	// requires width > 0;
	protected Window(/*@ non_null @*/ GenericWindow p)
	{
		super(1, 1);
		m_windowProcessor = p;
		m_queryable = p.getQueryable(toString(), p.getWidth());
	}
	
	//@ ensures \result > 0;
	/*@ pure @*/ public int getWidth()
	{
		return m_windowProcessor.getWidth();
	}
	
	@Override
	protected WindowQueryable getQueryable(int in_arity, int out_arity)
	{
		return m_windowProcessor.getQueryable(toString(), m_windowProcessor.getWidth());
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		Queue<Object[]> q = new ArrayDeque<Object[]>();
		m_windowProcessor.compute(inputs, q, m_context);
		outputs.addAll(q);
		return true;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_windowProcessor.reset();
	}

	@Override
	/*@ pure non_null @*/ public Window duplicate(boolean with_state) 
	{
		Window w = new Window(m_windowProcessor.duplicate(with_state));
		return (Window) copyInto(w, with_state);
	}

	protected abstract static class GenericWindow implements Printable, Readable, StateDuplicable<GenericWindow>
	{
		protected int m_windowWidth;
		
		/*@ non_null @*/ protected CircularBuffer<Object> m_window;
		
		static final transient String s_widthKey = "width";
		
		static final transient String s_windowKey = "window"; 
		
		public GenericWindow(int width)
		{
			super();
			m_windowWidth = width;
			m_window = new CircularBuffer<Object>(m_windowWidth);
		}
		
		//@ ensures \result > 0;
		/*@ pure @*/ public int getWidth()
		{
			return m_windowWidth;
		}
		
		public abstract void compute(Object[] o, Queue<Object[]> q, Context c);

		public abstract void reset();
		
		@Override
		public abstract GenericWindow duplicate();
		
		@Override
		public abstract GenericWindow duplicate(boolean with_state);
		
		public abstract WindowQueryable getQueryable(String reference, int width);
		
		static class WindowQueryable extends ProcessorQueryable
		{
			protected int m_windowWidth;
			
			public WindowQueryable(String reference, int width)
			{
				super(reference, 1, 1);
				m_windowWidth = width;
			}
		}
	}

	static class ProcessorWindow extends GenericWindow
	{
		/*@ non_null @*/ protected Processor m_processor;

		/*@ non_null @*/ protected Pushable m_pushable;

		/*@ non_null @*/ protected SinkLast m_sink;
		
		/*@ non_null @*/ protected ProcessorWindowQueryable m_queryable;
				
		static final transient String s_processorKey = "processor";

		public ProcessorWindow(/*@ non_null @*/ Processor p, int width)
		{
			super(width);
			m_processor = p;
			m_sink = new SinkLast();
			m_pushable = m_processor.getPushableInput();
			Connector.connect(m_processor, m_sink);
			m_queryable = getQueryable(p.toString(), width);
		}

		@Override
		public void compute(Object[] inputs, Queue<Object[]> outputs, Context c)
		{
			m_window.add(inputs[0]);
			if (m_window.isFull())
			{
				m_processor.reset();
				m_sink.reset();
				for (Object o : m_window)
				{
					m_pushable.push(o);
				}
				if (!m_sink.isEmpty())
				{
					outputs.add(new Object[] {m_sink.getLast()});
				}
				m_queryable.add(m_processor.getQueryable(), m_sink.getQueryable());
			}
		}

		@Override
		public void reset()
		{
			m_window.clear();
			m_processor.reset();
			m_sink.reset();
		}
		
		@Override
		public ProcessorWindow duplicate()
		{
			return duplicate(false);
		}
		
		@Override
		public ProcessorWindow duplicate(boolean with_state)
		{
			ProcessorWindow gw = new ProcessorWindow(m_processor.duplicate(with_state), m_windowWidth);
			if (with_state)
			{
				gw.m_window = m_window.duplicate(with_state);
			}
			return gw;
		}

		@Override
		public Object print(ObjectPrinter<?> printer) throws PrintException
		{
			Map<String,Object> map = new HashMap<String,Object>();
			map.put(GenericWindow.s_widthKey, m_windowWidth);
			map.put(GenericWindow.s_windowKey, m_window);
			map.put(s_processorKey, m_processor);
			return map;
		}

		@SuppressWarnings("unchecked")
		@Override
		public ProcessorWindow read(ObjectReader<?> reader, Object o) throws ReadException
		{
			Object r_o = reader.read(o);
			if (r_o == null || !(r_o instanceof Map))
			{
				throw new ReadException("Unexpected object format");
			}
			try
			{
				Map<String,Object> map = (Map<String,Object>) r_o;
				if (!map.containsKey(s_widthKey) || !map.containsKey(s_windowKey) 
						|| !map.containsKey(s_processorKey))
				{
					throw new ReadException("Unexpected map format");
				}
				int width = (Integer) map.get(s_widthKey);
				CircularBuffer<Object> window = (CircularBuffer<Object>) map.get(s_windowKey);
				Processor processor = (Processor) map.get(s_processorKey);
				ProcessorWindow pw = new ProcessorWindow(processor, width);
				pw.m_window = window;
				return pw;
			}
			catch (ClassCastException cce)
			{
				throw new ReadException(cce);
			}
		}

		@Override
		public ProcessorWindowQueryable getQueryable(String reference, int width) 
		{
			return new ProcessorWindowQueryable(reference, width);
		}
		
		static class ProcessorWindowQueryable extends WindowQueryable
		{
			/*@ non_null @*/ protected List<Queryable> m_processorQueryables;
			
			/*@ non_null @*/ protected List<Queryable> m_sinkQueryables;
			
			public ProcessorWindowQueryable(String reference, int width)
			{
				super(reference, width);
				m_processorQueryables = new ArrayList<Queryable>();
				m_sinkQueryables = new ArrayList<Queryable>();
			}
			
			public void add(/*@ non_null @*/ Queryable processor_q, /*@ non_null @*/ Queryable sink_q)
			{
				m_processorQueryables.add(processor_q);
				m_sinkQueryables.add(sink_q);
			}
			
			@Override
			protected List<TraceabilityNode> queryOutput(TraceabilityQuery q, int out_index, 
					Designator tail, TraceabilityNode root, Tracer factory)
			{
				Designator head_t = tail.peek();
				Designator tail_t = tail.tail();
				if (!(head_t instanceof NthEvent))
				{
					return unknownLink(root, factory);
				}
				int num_event = ((NthEvent) head_t).getIndex();
				Tracer sub_factory = factory.getSubTracer(num_event);
				if (m_processorQueryables.size() <= num_event)
				{
					return unknownLink(root, factory);
				}
				Queryable sink_q = m_sinkQueryables.get(num_event);
				ComposedDesignator cd = new ComposedDesignator(tail_t, SinkContents.instance, new NthElement(0), new NthOutput(0));
				List<TraceabilityNode> leaves = sink_q.query(q, cd, root, sub_factory);
				// Connect each leaf to the window's actual input
				List<TraceabilityNode> new_leaves = new ArrayList<TraceabilityNode>();
				for (TraceabilityNode leaf : leaves)
				{
					// TODO
				}
				return new_leaves;
			}

			@Override
			protected List<TraceabilityNode> queryInput(TraceabilityQuery q, int in_index, Designator tail, TraceabilityNode root, Tracer factory)
			{
				return unknownLink(root, factory);
			}
		}
	}

	static class SlidableWindow extends GenericWindow
	{
		/*@ non_null @*/ protected SlidableFunction m_function;
		
		protected static final transient String s_functionKey = "function";

		public SlidableWindow(SlidableFunction f, int width)
		{
			super(width);
			m_function = f;
			m_window = new CircularBuffer<Object>(m_windowWidth);
		}

		@Override
		public void compute(Object[] o, Queue<Object[]> q, Context c)
		{
			boolean was_full = m_window.isFull();
			Object o_out = m_window.add(o[0]);
			Object[] outs = new Object[1];
			if (was_full)
			{
				m_function.devaluate(new Object[] {o_out}, outs, c);
			}
			m_function.evaluate(o, outs, c);
			if (was_full || m_window.isFull())
			{
				q.add(outs);
			}
		}

		@Override
		public void reset()
		{
			m_function.reset();
			m_window.clear();
		}
		
		@Override
		public SlidableWindow duplicate()
		{
			return duplicate(false);
		}
		
		@Override
		public SlidableWindow duplicate(boolean with_state)
		{
			SlidableWindow sw = new SlidableWindow((SlidableFunction) m_function.duplicate(with_state), m_windowWidth);
			if (with_state)
			{
				sw.m_window = m_window.duplicate(with_state);
			}
			return sw;
		}

		@Override
		public Map<String,Object> print(ObjectPrinter<?> printer) throws PrintException 
		{
			Map<String,Object> map = new HashMap<String,Object>();
			map.put(GenericWindow.s_widthKey, m_windowWidth);
			map.put(GenericWindow.s_windowKey, m_window);
			map.put(s_functionKey, m_function);
			return map;
		}

		@SuppressWarnings("unchecked")
		@Override
		public SlidableWindow read(ObjectReader<?> reader, Object o) throws ReadException
		{
			Object r_o = reader.read(o);
			if (r_o == null || !(r_o instanceof Map))
			{
				throw new ReadException("Unexpected object format");
			}
			try
			{
				Map<String,Object> map = (Map<String,Object>) r_o;
				if (!map.containsKey(s_widthKey) || !map.containsKey(s_windowKey) || !map.containsKey(s_functionKey))
				{
					throw new ReadException("Unexpected map format");
				}
				int width = (Integer) map.get(s_widthKey);
				CircularBuffer<Object> window = (CircularBuffer<Object>) map.get(s_windowKey);
				SlidableFunction function = (SlidableFunction) map.get(s_functionKey);
				SlidableWindow sw = new SlidableWindow(function, width);
				sw.m_window = window;
				return sw;
			}
			catch (ClassCastException cce)
			{
				throw new ReadException(cce);
			}
		}

		@Override
		public SlidableWindowQueryable getQueryable(String reference, int width)
		{
			return new SlidableWindowQueryable(reference, width);
		}
		
		static class SlidableWindowQueryable extends WindowQueryable
		{
			public SlidableWindowQueryable(String reference, int width)
			{
				super(reference, width);
			}
		}
	}

	protected static class CircularBuffer<T> implements Iterable<T>, Printable, Readable, StateDuplicable<CircularBuffer<T>>
	{
		Object[] m_buffer;

		protected int m_head;

		protected int m_size = 0;
		
		static final transient String s_headKey = "head";
		
		static final transient String s_sizeKey = "size";
		
		static final transient String s_bufferKey = "buffer";

		public CircularBuffer(int width)
		{
			super();
			m_buffer = new Object[width];
			m_head = 0;
			m_size = 0;
		}

		public void clear()
		{
			m_head = 0;
			m_size = 0;
			for (int i = 0; i < m_buffer.length; i++)
			{
				m_buffer[i] = null;
			}
		}

		@SuppressWarnings("unchecked")
		public T add(Object o)
		{
			T old = null;
			if (m_size != 0)
			{
				m_head = (m_head + 1) % m_buffer.length;
			}
			if (m_size == m_buffer.length)
			{
				old = (T) m_buffer[m_head];
			}
			m_buffer[m_head] = o;
			m_size = Math.min(m_size + 1, m_buffer.length);
			return old;
		}

		public boolean isFull()
		{
			return m_size == m_buffer.length;
		}

		@Override
		public Iterator<T> iterator()
		{
			return new CircularBufferIterator();
		}

		public class CircularBufferIterator implements Iterator<T>
		{
			protected int m_index;

			protected boolean m_running;

			public CircularBufferIterator()
			{
				super();
				if (isFull())
				{
					m_index = (m_head + 1) % m_buffer.length;
				}
				else
				{
					m_index = 0;
				}
				m_running = (m_buffer.length > 0);
			}

			@Override
			public boolean hasNext() 
			{
				return m_running && m_buffer[m_index] != null;
			}

			@SuppressWarnings("unchecked")
			@Override
			public T next() 
			{
				if (!m_running)
				{
					throw new NoSuchElementException();
				}
				if (m_index == m_head)
				{
					// We returned to the head: done enumerating
					m_running = false;
				}
				T t = (T) m_buffer[m_index];
				m_index = (m_index + 1) % m_buffer.length;
				return t;
			}
			
			@Override
			public void remove()
			{
				throw new UnsupportedOperationException("Operation remove not supported on a circular buffer");
			}
		}

		@Override
		public CircularBuffer<T> duplicate() 
		{
			return duplicate(false);
		}

		@Override
		public CircularBuffer<T> duplicate(boolean with_state) 
		{
			CircularBuffer<T> cb = new CircularBuffer<T>(m_buffer.length);
			if (with_state)
			{
				cb.m_size = m_size;
				cb.m_head = m_head;
				for (int i = 0; i < m_buffer.length; i++)
				{
					cb.m_buffer[i] = m_buffer[i];
				}
			}
			return cb;
		}

		@SuppressWarnings("unchecked")
		@Override
		public CircularBuffer<T> read(ObjectReader<?> reader, Object o) throws ReadException
		{
			Object r_o = reader.read(o);
			if (r_o == null || !(r_o instanceof Map))
			{
				throw new ReadException("Unexpected object format");
			}
			try
			{
				Map<String,Object> map = (Map<String,Object>) r_o;
				if (!map.containsKey(s_headKey) || !map.containsKey(s_sizeKey) || !map.containsKey(s_bufferKey))
				{
					throw new ReadException("Unexpected map format");
				}
				int head = (Integer) map.get(s_headKey);
				int size = (Integer) map.get(s_sizeKey);
				List<Object> buffer = (List<Object>) map.get(s_bufferKey);
				CircularBuffer<T> cb = new CircularBuffer<T>(buffer.size());
				cb.m_head = head;
				cb.m_size = size;
				for (int i = 0; i < cb.m_buffer.length; i++)
				{
					cb.m_buffer[i] = buffer.get(i);
				}
				return cb;
			}
			catch (ClassCastException cce)
			{
				throw new ReadException(cce);
			}
		}

		@Override
		public Map<String,Object> print(ObjectPrinter<?> printer) throws PrintException
		{
			Map<String,Object> map = new HashMap<String,Object>();
			map.put(s_headKey, m_head);
			map.put(s_sizeKey, m_size);
			List<Object> buffer = new ArrayList<Object>(m_buffer.length);
			for (int i = 0; i < m_buffer.length; i++)
			{
				buffer.add(m_buffer[i]);
			}
			map.put(s_bufferKey, buffer);
			return map;
		}
	}

	@Override
	protected Window readState(Object state, int in_arity, int out_arity) throws ReadException 
	{
		if (state == null || !(state instanceof GenericWindow))
		{
			throw new ReadException("Unexpected processor window");
		}
		return new Window((GenericWindow) state);
	}

	@Override
	protected GenericWindow printState() 
	{
		return m_windowProcessor;
	}
}