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

import java.util.Vector;

public class Mutator extends SingleProcessor
{
	/**
	 * The output event to send
	 */
	protected final Vector<Object> m_output;
	
	public Mutator(int in_arity, Vector<Object> v)
	{
		super(in_arity, v.size());
		m_output = v;
	}
	
	public Mutator(int in_arity, Object o)
	{
		super(in_arity, 1);
		m_output = new Vector<Object>();
		m_output.add(o);
	}

	@Override
	protected Vector<Object> compute(Vector<Object> inputs)
	{
		return m_output;
	}

}
