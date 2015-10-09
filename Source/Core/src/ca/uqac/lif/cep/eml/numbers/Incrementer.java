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
package ca.uqac.lif.cep.eml.numbers;

import java.util.Queue;

import ca.uqac.lif.cep.SingleProcessor;

public class Incrementer extends SingleProcessor
{
	protected final float m_increment;
	
	public Incrementer(float increment)
	{
		super(1, 1);
		m_increment = increment;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object[] outputs = new Object[inputs.length];
		short i = 0;
		for (Object in : inputs)
		{
			if (in instanceof Number)
			{
				Number n = (Number) in;
				n = n.floatValue() + m_increment;
				outputs[i] = n;
			}
			i++;
		}
		return wrapVector(outputs);
	}

}
