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

import java.util.ArrayDeque;
import java.util.Queue;

public abstract class Processor
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
	protected int m_outputArity;

	protected final Queue<Object>[] m_inputQueues;

	protected Queue<Object>[] m_outputQueues;

	protected Pullable[] m_inputPullables;

	protected Pushable[] m_outputPushables;

	protected static int s_uniqueIdCounter = 0;

	protected int m_uniqueId;

	/**
	 * Initializes a processor
	 * @param in_arity The input arity
	 * @param out_arity The output arity
	 */
	@SuppressWarnings("unchecked")
	public Processor(int in_arity, int out_arity)
	{
		super();
		m_inputArity = in_arity;
		m_outputArity = out_arity;
		m_uniqueId = s_uniqueIdCounter++;
		m_inputQueues = new Queue[m_inputArity];
		for (int i = 0; i < m_inputArity; i++)
		{
			m_inputQueues[i] = new ArrayDeque<Object>();
		}
		m_outputQueues = new Queue[m_outputArity];
		for (int i = 0; i < m_outputArity; i++)
		{
			m_outputQueues[i] = new ArrayDeque<Object>();
		}
		m_inputPullables = new Pullable[m_inputArity];
		m_outputPushables = new Pushable[m_outputArity];
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

	public static boolean allNull(Object[] v)
	{
		for (Object o : v)
		{
			if (o != null)
			{
				return false;
			}
		}
		return true;
	}
}
