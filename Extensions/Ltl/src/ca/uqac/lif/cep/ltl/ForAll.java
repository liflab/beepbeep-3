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
package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public class ForAll extends FirstOrderQuantifier
{
	public ForAll(Processor p, Function split_function, String var_name, Function domain)
	{
		super(p, split_function, var_name, domain);
	}

	@Override
	public Object evaluate(Object[] values) 
	{
		Value[] t_values = new Value[values.length];
		for (int i = 0; i < values.length; i++)
		{
			t_values[i] = Troolean.trooleanValue(values[i]);
		}
		return Troolean.and(t_values);
	}

	@Override
	public Processor clone() 
	{
		// TODO Auto-generated method stub
		return null;
	}

}
