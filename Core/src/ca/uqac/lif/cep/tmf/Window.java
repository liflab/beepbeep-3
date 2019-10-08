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
		m_queryable = new WindowQueryable(toString(), 1, 1);
	}
	
	//@ ensures \result > 0;
	/*@ pure @*/ public int getWidth()
	{
		return m_windowProcessor.getWidth();
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
		
		public GenericWindow(int width)
		{
			super();
			m_windowWidth = width;
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
	}

	static class ProcessorWindow extends GenericWindow
	{
		/*@ non_null @*/ protected Processor m_processor;

		/*@ non_null @*/ protected CircularBuffer<Object> m_window;

		/*@ non_null @*/ protected Pushable m_pushable;

		/*@ non_null @*/ protected SinkLast m_sink;

		public ProcessorWindow(/*@ non_null @*/ Processor p, int width)
		{
			super(width);
			m_processor = p;
			m_sink = new SinkLast();
			m_pushable = m_processor.getPushableInput();
			Connector.connect(m_processor, m_sink);
			m_window = new CircularBuffer<Object>(m_windowWidth);
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
			}
		}

		@Override
		public void reset()
		{
			m_window.clear();
			m_processor.reset();
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
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException
		{
			// TODO Auto-generated method stub
			return null;
		}
	}

	static class SlidableWindow extends GenericWindow
	{
		/*@ non_null @*/ protected SlidableFunction m_function;
		
		/*@ non_null @*/ protected CircularBuffer<Object> m_window;

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
		public Object print(ObjectPrinter<?> printer) throws PrintException {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Object read(ObjectReader<?> reader, Object o) throws ReadException {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	public static class WindowQueryable extends ProcessorQueryable
	{
		public WindowQueryable(String reference, int in_arity, int out_arity)
		{
			super(reference, in_arity, out_arity);
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
				if (buffer.size() != size)
				{
					throw new ReadException("Unexpected buffer size");
				}
				CircularBuffer<T> cb = new CircularBuffer<T>(size);
				cb.m_head = head;
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