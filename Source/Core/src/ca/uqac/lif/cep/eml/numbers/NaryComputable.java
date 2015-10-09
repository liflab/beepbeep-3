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

import ca.uqac.lif.cep.Computable;

public abstract class NaryComputable implements Computable
{
	protected final int m_inputArity;
	
	public NaryComputable(int arity)
	{
		super();
		m_inputArity = arity;
	}

	@Override
	public final int getInputArity()
	{
		return m_inputArity;
	}

	@Override
	public final int getOutputArity()
	{
		return 1;
	}
	
	@Override
	public final Object[] compute(Object[] inputs)
	{
		Number[] numbers = new Number[inputs.length];
		short i = 0;
		for (Object o : inputs)
		{
			if (o instanceof Number)
			{
				numbers[i] = (Number) o;
			}
			else
			{
				numbers[i] = 0;
			}
			i++;
		}
		return computeNumerical(numbers);
	}
	
	protected abstract Object[] computeNumerical(Number[] inputs);
	
	public NaryComputable newInstance()
	{
		// TODO
		return null;
	}
}
