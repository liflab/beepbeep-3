/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep;

import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

public abstract class Processor implements Buildable
{
	/**
	 * The processor's input arity, i.e. the number of input events it requires
	 * to produce an output
	 */
	protected final int m_inputArity;
	
	/**
	 * The processor's output arity, i.e. the number of output
	 * events it produces
	 */
	protected final int m_outputArity;
	
	protected Vector<Queue<Object>> m_inputQueues;
	
	protected Vector<Queue<Object>> m_outputQueues;
	
	protected Vector<Pullable> m_inputPullables;
	
	protected Vector<Pushable> m_outputPushables;
	
	protected static int s_uniqueIdCounter = 0;
	
	protected int m_uniqueId;
	
	public Processor()
	{
		super();
		m_inputArity = 0;
		m_outputArity = 0;
	}

	/**
	 * Initializes a processor
	 * @param in_arity The input arity
	 * @param out_arity The output arity
	 */
	public Processor(int in_arity, int out_arity)
	{
		super();
		m_inputArity = in_arity;
		m_outputArity = out_arity;
		m_uniqueId = s_uniqueIdCounter++;
		reset();
	}
	
	@Override
	public int hashCode()
	{
		return m_uniqueId;
	}
	
	@Override
	public boolean equals(Object o)
	{
		if (!(o instanceof Processor))
		{
			return false;
		}
		Processor p = (Processor) o;
		return m_uniqueId == p.m_uniqueId;
	}
	
	/**
	 * Fetches the processor instance's unique ID
	 * @return The ID
	 */
	public int getId()
	{
		return m_uniqueId;
	}
	
	/**
	 * Resets the processor. This has for effect of flushing the contents
	 * of all input and output event queues. If the processor has an internal
	 * state, this also resets this state to its "initial" settings.
	 */
	public abstract void reset();
	
	public abstract Pushable getPushableInput(int index);
	
	public abstract Pullable getPullableOutput(int index);
	
	public abstract void setPullableInput(int i, Pullable p);
	
	public abstract void setPushableOutput(int i, Pushable p);
	
	public abstract Pushable getPushableOutput(int index);
	
	@Override
	public abstract void build(Stack<Object> stack);
	//{
		// Do nothing
	//}
	
	/**
	 * Returns the processor's input arity
	 * @return The arity
	 */
	public final int getInputArity()
	{
		return m_inputArity;
	}
	
	/**
	 * Returns the processor's output arity
	 * @return The arity
	 */
	public final int getOutputArity()
	{
		return m_outputArity;
	}
}
