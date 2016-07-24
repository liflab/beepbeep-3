package ca.uqac.lif.cep.ltl;

import java.util.ArrayDeque;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.epl.QueueSink;
import ca.uqac.lif.cep.functions.Function;

public class BooleanQuantifier extends SingleProcessor 
{
	/**
	 * The internal processor
	 */
	protected FirstOrderSpawn m_spawn;
	
	/**
	 * The instances of the spawn processor
	 */
	protected List<FirstOrderSpawn> m_instances;
	
	/**
	 * The input pushables of each instance
	 */
	protected List<Pushable> m_instancePushables;
	
	/**
	 * A sink for each instance
	 */
	protected List<QueueSink> m_sinks;
	
	/**
	 * A queue for each sink
	 */
	protected List<Queue<Object>> m_queues;	
	
	/**
	 * The name of the quantified variable
	 */
	protected String m_variableName;
	
	BooleanQuantifier()
	{
		super(1, 1);
		m_instances = new LinkedList<FirstOrderSpawn>();
		m_instancePushables = new LinkedList<Pushable>();
		m_sinks = new LinkedList<QueueSink>();
		m_queues = new LinkedList<Queue<Object>>();
	}
	
	public BooleanQuantifier(String var_name, FirstOrderSpawn spawn)
	{
		this();
		m_variableName = var_name;
		m_spawn = spawn;
	}
	
	public BooleanQuantifier(String var_name, Function split_function, Processor p, Function combine_function, Object value_empty)
	{
		this();
		m_variableName = var_name;
		m_spawn = new FirstOrderSpawn(var_name, split_function, p, combine_function, value_empty);
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs) 
	{
		Queue<Object[]> out_queue = new ArrayDeque<Object[]>();
		FirstOrderSpawn new_spawn = m_spawn.clone();
		new_spawn.setContext(m_context);
		m_instances.add(new_spawn);
		m_instancePushables.add(new_spawn.getPushableInput(0));
		QueueSink new_sink = new QueueSink(1);
		try 
		{
			Connector.connect(new_spawn, new_sink);
		} 
		catch (ConnectorException e) 
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		m_sinks.add(new_sink);
		m_queues.add(new_sink.getQueue(0));
		// Push event to all instances
		for (Pushable push : m_instancePushables)
		{
			push.push(inputs[0]);
		}
		// Check if some instance reached a result
		int max_fetch_count = m_instances.size();
		while (!m_instances.isEmpty() && max_fetch_count > 0)
		{
			max_fetch_count--;
			Queue<Object> queue = m_queues.get(0);
			if (!queue.isEmpty())
			{
				// This instance reached a value: remove it
				Object value = queue.remove();
				Object[] v = new Object[1];
				v[0] = value;
				out_queue.add(v);
				m_instances.remove(0);
				m_instancePushables.remove(0);
				m_sinks.remove(0);
				m_queues.remove(0);
			}
			else
			{
				// If this processor hasn't reached a verdict,
				// no use in processing the following
				break;
			}
		}
		return out_queue;
	}
	
	@Override
	public void setContext(Context context)
	{
		super.setContext(context);
		m_spawn.setContext(context);
	}
	
	@Override
	public void setContext(String key, Object value)
	{
		super.setContext(key, value);
		m_spawn.setContext(key, value);
	}

	@Override
	public BooleanQuantifier clone() 
	{
		return new BooleanQuantifier(m_variableName, m_spawn);
	}
	
	protected class FirstOrderSpawn extends Spawn
	{
		public FirstOrderSpawn(String var_name, Function split_function, Processor p, Function combine_function, Object value_empty)
		{
			super(p, split_function, combine_function);
			m_variableName = var_name;
			m_valueIfEmptyDomain = value_empty;
			//m_domainFunction = domain;
		}

		@Override
		public void addContextFromSlice(Processor p, Object slice) 
		{
			Object[] input = new Object[1];
			input[0] = slice;
			p.setContext(m_variableName, slice);
		}

		@Override
		public FirstOrderSpawn clone()
		{
			return new FirstOrderSpawn(m_variableName, m_splitFunction.clone(m_context), m_processor.clone(), m_combineProcessor.getFunction().clone(m_context), m_valueIfEmptyDomain);
		}
	}

}
