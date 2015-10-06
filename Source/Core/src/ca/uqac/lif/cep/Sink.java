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

public abstract class Sink extends SingleProcessor
{
	public Sink()
	{
		this(0);
	}
	
	public Sink(int in_arity)
	{
		super(in_arity, 0);
	}

	/**
	 * Tells the sink to pull events from the pipeline
	 */
	public final void pull()
	{
		Object[] inputs = new Object[getInputArity()];
		for (int i = 0; i < getInputArity(); i++)
		{
			Pullable p = m_inputPullables[i];
			inputs[i] = p.pull();
		}
		compute(inputs);
	}
	
	/**
	 * Tells the sink to pull events from the pipeline
	 */
	public final void pullHard()
	{
		Object[] inputs = new Object[getInputArity()];
		for (int i = 0; i < getInputArity(); i++)
		{
			Pullable p = m_inputPullables[i];
			inputs[i] = p.pullHard();
		}
		compute(inputs);
	}

}
