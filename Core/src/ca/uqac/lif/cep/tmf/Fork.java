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

import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.UniformProcessor;
import ca.uqac.lif.cep.objectfactory.IntegerSetting;
import ca.uqac.lif.cep.objectfactory.SettingsSet;

/**
 * Duplicates an input trace into two or more output traces.
 * 
 * @author Sylvain Hallé
 *
 */
public class Fork extends UniformProcessor
{
	public Fork(int out_arity)
	{
		super(1, out_arity);
	}

	@Override
	public Fork clone()
	{
		return new Fork(getOutputArity());
	}

	@Override
	protected boolean compute(Object[] inputs, Object[] outputs)
	{
		int arity = getOutputArity();
		for (int i = 0; i < arity; i++)
		{
			outputs[i] = inputs[0];
		}
		return true;
	}

	/**
	 * Creates a copy of the current fork with a greater arity
	 * @param out_arity The desired arity for the output fork
	 */
	@SuppressWarnings("unchecked")
	public void extendOutputArity(int out_arity)
	{
		m_outputArray = new Object[out_arity];
		m_outputQueues = new Queue[out_arity];
		m_outputArity = out_arity;
		for (int i = 0; i < m_outputArity; i++)
		{
			m_outputQueues[i] = new ArrayDeque<Object>();
		}
		Pushable[] out_pushables = new Pushable[out_arity];
		for (int i = 0; i < m_outputPushables.length; i++)
		{
			out_pushables[i] = m_outputPushables[i];
		}
		m_outputPushables = out_pushables;
	}

	/**
	 * Gets the set of initial settings for this processor
	 * @return The set of settings
	 */
	public static SettingsSet getInitialSettings()
	{
		SettingsSet set = new SettingsSet(Window.class);
		set.add(new IntegerSetting("branches", true, "The number of branches in which the output is to be split"));
		return set;
	}

	/**
	 * Creates a new instance of this object based on a set of
	 * instantiation settings
	 * @param s The settings
	 * @return A new instance of the object
	 */
	public static Fork getNewInstance(SettingsSet s) throws InstantiationException
	{
		int branches = ((IntegerSetting) s.get("branches")).getIntValue();
		Fork out = new Fork(branches);
		return out;
	}
}
