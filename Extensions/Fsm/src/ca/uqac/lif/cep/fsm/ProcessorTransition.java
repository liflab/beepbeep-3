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
package ca.uqac.lif.cep.fsm;

import java.util.Queue;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.epl.QueueSink;
import ca.uqac.lif.cep.tuples.EmlBoolean;

/**
 * Represents a transition in the Moore machine.  
 * Using this transition actually creates a generalized Moore machine, as
 * the labels on each
 * transition are themselves <em>processors</em>: not only can they express
 * complex conditions on the input event, but they can also have a
 * state. This was done mainly because it was handy to just use the class
 * <code>Processor</code> to evaluate conditions (send the event to the processor
 * and just collect its output), rather than come up with special objects to
 * do that.
 * <p>
 * A "classical" Moore machine is a particular case where all processors
 * for expressing the conditions are unary and stateless.
 * @author Sylvain Hallé
 *
 */
public class ProcessorTransition extends MooreMachine.Transition
{
	/**
	 * The condition for taking that transition. This is materialized by
	 * a processor, which is expected to return true or false on the input
	 * we feed it.
	 */
	final Processor m_condition;
	
	/**
	 * The condition's input pushables
	 */
	final Pushable[] m_pushables;
	
	/**
	 * The sink used to get the processor's output
	 */
	final QueueSink m_sink;
	
	/**
	 * The state one will be in if the condition evaluates to true
	 */
	final int m_destination;
	
	public ProcessorTransition(ProcessorTransition pt) throws ConnectorException
	{
		this(pt.m_destination, pt.m_condition.clone());
	}
	
	/**
	 * Instantiates a new transition
	 * @param condition The condition for taking that transition
	 * @param destination The state one will be in if the condition 
	 *   evaluates to true
	 */
	public ProcessorTransition(int destination, Processor condition) throws ConnectorException
	{
		super();
		m_destination = destination;
		m_condition = condition;
		m_pushables = new Pushable[m_condition.getInputArity()];
		for (int i = 0; i < m_pushables.length; i++)
		{
			m_pushables[i] = m_condition.getPushableInput(i);
		}
		m_sink = new QueueSink(m_condition.getOutputArity());
		Connector.connect(m_condition, m_sink);
	}
	
	public boolean isFired(Object[] inputs)
	{
		// First, push the inputs into the processor
		for (int i = 0; i < inputs.length; i++)
		{
			m_pushables[i].push(inputs[i]);
		}
		// Second, collect its output
		Queue<Object> q = m_sink.getQueue(0);
		if (q.isEmpty())
		{
			// The sink did not collect anything, so this transition does not fire
			return false;
		}
		// The sink collected something: get it
		Object output = q.remove();
		if (output == null)
		{
			// Nothing interesting
			return false;
		}
		// Try to do something with the first output
		return EmlBoolean.parseBoolValue(output);
	}
	
	@Override
	public int getDestination()
	{
		return m_destination;
	}
	
	@Override
	public void reset()
	{
		m_condition.reset();
		m_sink.reset();
	}
	
	@Override
	public String toString()
	{
		return m_condition + " -> " + m_destination;
	}
	
}
