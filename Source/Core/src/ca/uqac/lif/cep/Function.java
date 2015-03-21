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

public class Function extends Processor
{
	/**
	 * The object responsible for the computation
	 */
	protected final Computable m_compute;
	
	public Function(Computable comp)
	{
		super(comp.getInputArity(), comp.getOutputArity());
		m_compute = comp;
	}

	@Override
	protected Vector<Object> compute(Vector<Object> inputs)
	{
		return m_compute.compute(inputs);
	}

}
