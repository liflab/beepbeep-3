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
package ca.uqac.lif.cep.tmf;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.numbers.EmlNumber;
import ca.uqac.lif.cep.objectfactory.IntegerSetting;
import ca.uqac.lif.cep.objectfactory.SettingsSet;

/**
 * Returns one input event and discards the next <i>n</i>-1. The value <i>n</i>
 * is called the <em>decimation interval</em>.
 * 
 * @author Sylvain Hallé
 */
public class CountDecimate extends SingleProcessor
{
	/**
	 * The decimation interval
	 */
	protected final int m_interval;

	/**
	 * Index of last event received
	 */
	protected int m_current;

	public CountDecimate()
	{
		this(1);
	}

	public CountDecimate(int interval)
	{
		super(1, 1);
		m_interval = interval;
		m_current = 0;
	}

	@Override
	public void reset()
	{
		super.reset();
		m_current = 0;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object[] out = null;
		if (m_current == 0)
		{
			out = inputs;
		}
		m_current = (m_current + 1) % m_interval;
		if (out == null)
		{
			return new ArrayDeque<Object[]>();
		}
		return wrapVector(out);
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		//stack.pop(); // (
		Processor p = (Processor) stack.pop();
		//stack.pop(); // )
		stack.pop(); // OF
		stack.pop(); // TH
		EmlNumber interval = (EmlNumber) stack.pop();
		stack.pop(); // EVERY
		CountDecimate out = new CountDecimate(interval.intValue());
		Connector.connect(p, out);
		stack.push(out);
	}

	@Override
	public CountDecimate clone()
	{
		return new CountDecimate(m_interval);
	}

	/**
	 * Gets the set of initial settings for this processor
	 * @return The set of settings
	 */
	public static SettingsSet getInitialSettings()
	{
		SettingsSet set = new SettingsSet(Window.class);
		set.add(new IntegerSetting("step", true, "The number of events to discard"));
		return set;
	}

	/**
	 * Creates a new instance of this object based on a set of
	 * instantiation settings
	 * @param s The settings
	 * @return A new instance of the object
	 */
	public static CountDecimate getNewInstance(SettingsSet s) throws InstantiationException
	{
		int step = ((IntegerSetting) s.get("step")).getIntValue();
		CountDecimate out = new CountDecimate(step);
		return out;
	}
}
