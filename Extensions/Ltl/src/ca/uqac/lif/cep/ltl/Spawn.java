package ca.uqac.lif.cep.ltl;

import java.util.Collection;
import java.util.HashSet;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Mutator;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SmartFork;
import ca.uqac.lif.cep.epl.NaryToArray;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionProcessor;

public class Spawn extends Processor
{	
	/**
	 * The internal processor to evaluate the quantifier on
	 */
	protected Processor m_processor;

	/**
	 * The function to evaluate to create each instance of the quantifier.
	 * This function must return a <code>Collection</code> of objects;
	 * one instance of the internal processor will be created for each
	 * element of the collection.
	 */
	protected Function m_splitFunction;

	/**
	 * Each instance of the processor spawned by the evaluation of the
	 * quantifier
	 */
	protected Processor[] m_instances;
	
	/**
	 * The fork used to split the input to the multiple instances of the
	 * processor
	 */
	protected SmartFork m_fork;

	/**
	 * The passthrough synchronizing the output of each processor instance
	 */
	protected NaryToArray m_joinProcessor;

	/**
	 * The function processor used to combine the values of each
	 * instance 
	 */
	protected FunctionProcessor m_combineProcessor;
	
	/**
	 * The pushable that will detect when the first event comes
	 */
	protected SentinelPushable m_inputPushable;
	
	/**
	 * The pullable that will detect when the first event is requested
	 */
	protected SentinelPullable m_outputPullable;
	
	/**
	 * Whether the split function generated any values
	 */
	protected boolean m_emptyDomain = false;
	
	/**
	 * The value to output if the spawn ranges over the empty set
	 */
	protected Object m_valueIfEmptyDomain = null;
	
	private Spawn()
	{
		super(1, 1);
	}

	public Spawn(Processor p, Function split_function, Function combine_function)
	{
		super(1, 1);
		m_processor = p;
		m_splitFunction = split_function;
		m_combineProcessor = new FunctionProcessor(combine_function);
		m_combineProcessor.setContext(m_context);
		m_instances = null;
		m_fork = null;
		m_inputPushable = new SentinelPushable();
		m_outputPullable = new SentinelPullable();
		//m_processor.setPullableInput(0, m_outputPullable);
	}
	
	/**
	 * Sets the value to output if the spawn ranges over the empty set
	 * @param value The value
	 */
	public void setValueIfEmptyDomain(Object value)
	{
		m_valueIfEmptyDomain = value;
	}
	
	@Override
	public Pushable getPushableInput(int index)
	{
		if (index != 0)
		{
			return null;
		}
		return m_inputPushable;
	}
	
	@Override
	public void setContext(Context context)
	{
		super.setContext(context);
		m_combineProcessor.setContext(context);
		m_splitFunction.setContext(context);
	}
	
	@Override
	public void setContext(String key, Object value)
	{
		super.setContext(key, value);
		m_combineProcessor.setContext(key, value);
		m_splitFunction.setContext(key, value);
	}
	
	@Override
	public void setPullableInput(int index, Pullable p)
	{
		m_inputPushable.setPullable(p);
	}
	
	@Override
	public Pullable getPullableOutput(int index)
	{
		if (index != 0)
		{
			return null;
		}
		return m_outputPullable;
	}
	
	@Override
	public void setPushableOutput(int index, Pushable p)
	{
		//m_outputPullable.setPushable(p);
		m_outputPullable.setPushable(p);
	}
	
	protected class SentinelPushable implements Pushable
	{
		protected Pushable m_pushable = null;
		
		protected Pullable m_pullable = null;
		
		public SentinelPushable()
		{
			super();
		}
		
		public void setPushable(Pushable p)
		{
			m_pushable = p;
			if (m_fork != null && m_pullable != null)
			{
				m_fork.setPullableInput(0, m_pullable);
			}
		}

		@Override
		public Pushable push(Object o)
		{
			if (m_pushable == null)
			{
				spawn(o);
			}
			return m_pushable.push(o);
		}

		@Override
		public int getPushCount()
		{
			if (m_pushable == null)
			{
				return 0;
			}
			return m_pushable.getPushCount();
		}

		@Override
		public Processor getProcessor() 
		{
			return Spawn.this;
		}

		@Override
		public int getPosition() 
		{
			return 0;
		}
		
		public void setPullable(Pullable p)
		{
			m_pullable = p;
			if (m_fork != null)
			{
				m_fork.setPullableInput(0, m_pullable);
			}
		}
		
		public Pullable getPullable()
		{
			return m_pullable;
		}
	}
	
	protected class SentinelPullable implements Pullable
	{
		protected Pullable m_pullable = null;
		
		protected Pushable m_pushable = null;
		
		public SentinelPullable()
		{
			super();
		}
		
		@Override
		public Object pull()
		{
			if (m_pullable == null)
			{
				Object o = m_inputPushable.getPullable().pullHard();
				spawn(o);
				// Re-put o in fork's queue so that it can process it
				m_fork.putInQueue(o);
				//m_fork.getPushableInput(0).push(o);
			}
			return m_pullable.pull();
		}

		@Override
		public Object pullHard()
		{
			if (m_pullable == null)
			{
				Object o = m_inputPushable.getPullable().pullHard();
				//System.out.println("Getting " + o);
				spawn(o);
				// Re-put o in fork's queue so that it can process it
				m_fork.putInQueue(o);
				//m_fork.getPushableInput(0).push(o);
			}
			return m_pullable.pullHard();
		}

		@Override
		public NextStatus hasNext()
		{
			if (m_pullable == null)
			{
				Object o = m_inputPushable.getPullable().pullHard();
				spawn(o);
				// Re-put o in fork's queue so that it can process it
				m_fork.putInQueue(o);
				//m_fork.getPushableInput(0).push(o);
			}
			return m_pullable.hasNext();
		}

		@Override
		public NextStatus hasNextHard()
		{
			if (m_pullable == null)
			{
				Object o = m_inputPushable.getPullable().pullHard();
				spawn(o);
				// Re-put o in fork's queue so that it can process it
				m_fork.putInQueue(o);
				//m_fork.getPushableInput(0).push(o);
			}
			return m_pullable.hasNextHard();
		}

		@Override
		public int getPullCount() 
		{
			return m_pullable.getPullCount();
		}

		@Override
		public Processor getProcessor()
		{
			return Spawn.this;
		}

		@Override
		public int getPosition()
		{
			return 0;
		}
		
		public void setPullable(Pullable p)
		{
			m_pullable = p;
			if (m_combineProcessor != null && m_pushable != null)
			{
				m_combineProcessor.setPushableOutput(0, m_pushable);
			}
		}
		
		public void setPushable(Pushable p)
		{
			m_pushable = p;
			if (m_combineProcessor != null)
			{
				m_combineProcessor.setPushableOutput(0, m_pushable);
			}
		}
		
		public Pushable getPushable()
		{
			return m_pushable;
		}
	}
	
	protected boolean spawn(Object o)
	{
		try 
		{
			Collection<?> values = getDomain(o);
			int size = values.size();
			if (size == 0)
			{
				// Domain is empty: processor returns a fixed value
				Mutator mutator = new Mutator(m_valueIfEmptyDomain, 1);
				m_inputPushable.setPushable(mutator.getPushableInput(0));
				mutator.setPullableInput(0, m_inputPushable.getPullable());
				m_outputPullable.setPullable(mutator.getPullableOutput(0));
				mutator.setPushableOutput(0, m_outputPullable.getPushable());
			}
			else
			{
				// Create a fork for as many values in the domain
				m_fork = new SmartFork(values.size());
				m_inputPushable.setPushable(m_fork.getPushableInput(0));
				m_instances = new Processor[size];
				// Create a join to collate the output of each spawned instance
				m_joinProcessor = new NaryToArray(size);
				m_joinProcessor.setContext(m_context);
				// Spawn one new internal processor per value
				int i = 0;
				for (Object slice : values)
				{
					Processor new_p = m_processor.clone();
					new_p.setContext(m_context);
					addContextFromSlice(new_p, slice);
					m_instances[i] = new_p;
					// Connect its input to the fork
					Connector.connect(m_fork, new_p, i, 0);
					// Connect its output to the join
					Connector.connect(new_p, m_joinProcessor, 0, i);
					i++;
				}
				Connector.connect(m_joinProcessor, m_combineProcessor, 0, 0);
				m_outputPullable.setPullable(m_combineProcessor.getPullableOutput(0));
			}
		}
		catch (ConnectorException e) 
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return true;
	}
	
	@SuppressWarnings("unchecked")
	protected /*@NotNull*/ Collection<Object> getDomain(Object o)
	{
		/* TODO: there are *lots* of null checks in this method, just to
		 * fend off whatever the split function returns. A couple of these
		 * checks could probably be removed, given the proper preconditions.
		 */
		Object[] inputs = new Object[1];
		inputs[0] = o;
		Object[] function_value = m_splitFunction.evaluate(inputs, m_context);
		Collection<Object> values = new HashSet<Object>();
		Object value = function_value[0];
		if (value == null)
		{
			return values;
		}
		if (value instanceof Collection)
		{
			Collection<Object> coll = (Collection<Object>) value;
			for (Object element : coll)
			{
				if (element != null)
				{
					values.add(element);
				}
			}
		}
		else
		{
			values.add(function_value[0]);
		}
		return values;
	}

	public void addContextFromSlice(Processor p, Object slice)
	{
		// Do nothing
	}
	
	@Override
	public Spawn clone()
	{
		Spawn out = new Spawn(m_processor.clone(), m_splitFunction.clone(m_context), m_combineProcessor.getFunction().clone(m_context));
		out.setContext(m_context);
		out.m_valueIfEmptyDomain = m_valueIfEmptyDomain;
		return out;
	}
}
