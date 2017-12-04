/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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

import java.util.Queue;

import ca.uqac.lif.cep.SingleProcessor;

/**
 * A sink that calls a method when a new front of events is pushed
 * to it. Override that method to do some processing on these events.
 * 
 * @author Sylvain Hallé
 *
 */
@SuppressWarnings("squid:S2160")
public class CallbackSink extends SingleProcessor 
{
	public CallbackSink(int in_arity)
	{
		super(in_arity, 0);
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		processEvents(inputs);
		return true;
	}

	@Override
	public CallbackSink duplicate() 
	{
		return new CallbackSink(getInputArity());
	}
	
	public void processEvents(Object[] inputs)
	{
		// Do nothing
	}
}
