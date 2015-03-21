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

public abstract class Combiner extends SingleProcessor
{
	protected Vector<Object> m_total;
	
	public Combiner(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
		m_total = initialize();
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_total = initialize(); 
	}

	@Override
	protected Vector<Object> compute(Vector<Object> inputs)
	{
		m_total = combine(inputs, m_total);
		return m_total;
	}
	
	protected abstract Vector<Object> initialize();
	
	protected abstract Vector<Object> combine(Vector<Object> inputs, Vector<Object> total);

}
