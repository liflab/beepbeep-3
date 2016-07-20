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
package ca.uqac.lif.cep.ltl;

import java.util.Collection;
import java.util.LinkedList;
import java.util.Queue;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.epl.NaryToArray;
import ca.uqac.lif.cep.epl.QueueSink;
import ca.uqac.lif.cep.functions.Function;

public abstract class Spawn extends SingleProcessor 
{
	/**
	 * The internal processor to evaluate the quantifier on
	 */
	protected Processor m_processor;
	
	/**
	 * Each instance of the processor spawned by the evaluation of the
	 * quantifier
	 */
	protected Processor[] m_instances;
	
	/**
	 * The passthrough synchronizing the output of each processor instance
	 */
	protected NaryToArray m_join;
	
	/**
	 * The sink collecting the output of each processor instance
	 */
	protected QueueSink m_sink;
	
	/**
	 * The function to evaluate to create each instance of the quantifier.
	 * This function must return a <code>Collection</code> of objects;
	 * one instance of the internal processor will be created for each
	 * element of the collection.
	 */
	protected Function m_function;
	
	/**
	 * Instantiates a new quantifier
	 * @param p The processor to evaluate the quantifier on
	 */
	public Spawn(Processor p, Function split_function)
	{
		super(p.getInputArity(), 1);
		m_processor = p;
		m_instances = null;
		m_function = split_function;
	}
	
	@Override
	public Queue<Object[]> compute(Object[] inputs)
	{
		if (m_instances == null)
		{
			spawn(inputs);
		}
		// Pass current event to each processor
		for (Processor p : m_instances)
		{
			for (int i = 0; i < inputs.length; i++)
			{
				Pushable pushable = p.getPushableInput(i);
				pushable.push(inputs[i]);
			}
		}
		// Retrieve event from each queue
		Queue<Object> queue = m_sink.getQueue(0);
		Queue<Object[]> out_queue = new LinkedList<Object[]>();
		while (!queue.isEmpty())
		{
			Object[] values = (Object[]) queue.remove();
			Object o = evaluate(values);
			Object[] o_a = new Object[1];
			o_a[0] = o;
			out_queue.add(o_a);
		}
		return out_queue;
	}
	
	/**
	 * From the current input events, creates one instance of the internal
	 * processor for each slice computed by the slicing function
	 * @param inputs The input events
	 */
	protected void spawn(Object[] inputs)
	{
		Object[] function_value = m_function.evaluate(inputs, m_context);
		if (function_value[0] instanceof Collection)
		{
			Collection<?> collection = (Collection<?>) function_value[0];
			m_instances = new Processor[collection.size()];
			m_join = new NaryToArray(collection.size());
			m_sink = new QueueSink(1);
			int i = 0;
			for (Object slice : collection)
			{
				createAndConnect(i++, slice);
			}
			try 
			{
				Connector.connect(m_join, m_sink);
			} 
			catch (ConnectorException e) 
			{
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		else
		{
			// The function returned a single element which is not a
			// collection: create a single instance with that value
			m_instances = new Processor[1];
			createAndConnect(0, function_value);
		}
	}
	
	protected void createAndConnect(int index, Object slice)
	{
		Processor new_p = m_processor.clone();
		new_p.setContext(m_context);
		addContextFromSlice(new_p, slice);
		m_instances[index] = new_p;
		try 
		{
			Connector.connect(new_p, m_join, 0, index);
		} 
		catch (ConnectorException e) 
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	public abstract void addContextFromSlice(Processor p, Object slice);
	
	public abstract Object evaluate(Object[] values);
}
