/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hall�

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
package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public class ForAll extends FirstOrderQuantifier
{
	public ForAll(String var_name, Function split_function, Processor p)
	{
		super(var_name, split_function, p, ArrayAnd.instance);
	}

	@Override
	public ForAll clone() 
	{
		ForAll out = new ForAll(m_variableName, m_spawn.m_splitFunction.clone(m_context), m_spawn.m_processor.clone());
		out.setContext(m_context);
		return out;
	}
	
	public static class ArrayAnd extends ArrayTroolean
	{
		public static final transient ArrayAnd instance = new ArrayAnd();
		
		@Override
		public Value[] compute(Object[] inputs)
		{
			Value[] out = new Value[1];
			Object[] val_array = (Object[]) inputs[0];
			out[0] = Troolean.and(Troolean.trooleanValues(val_array));
			return out;
		}

		@Override
		public Function clone()
		{
			return this;
		}
	}
	
	@Override
	public String toString()
	{
		return "forall " + m_variableName + " in " + m_spawn.m_splitFunction.toString();
	}
}
