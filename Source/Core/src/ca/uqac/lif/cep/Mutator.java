/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain HallÃ©

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

public class Mutator extends SingleProcessor
{
	/**
	 * The output event to send
	 */
	protected final Object[] m_output;
	
	public Mutator(int in_arity, Object[] v)
	{
		super(in_arity, v.length);
		m_output = v;
	}
	
	public Mutator(int in_arity, Object o)
	{
		super(in_arity, 1);
		m_output = new Object[1];
		m_output[0] = o;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		return wrapVector(m_output);
	}

	public static void build(Stack<Object> stack)
	{
		// TODO
	}

}
