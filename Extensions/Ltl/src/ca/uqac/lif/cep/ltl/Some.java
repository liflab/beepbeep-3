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

public class Some extends TrooleanQuantifier
{
	Some()
	{
		super();
		m_valueIfEmptyDomain = Troolean.Value.FALSE;
	}
	
	public Some(String var_name, Function split_function, Processor p)
	{
		super(var_name, split_function, p, ArrayOr.instance, Troolean.Value.FALSE);
		m_valueIfEmptyDomain = Troolean.Value.FALSE;
	}

	@Override
	public Some clone() 
	{
		Some out = new Some();
		super.cloneInto(out);
		out.m_variableName = m_variableName;
		out.setContext(m_context);
		return out;
	}
	
	@Override
	public String toString()
	{
		return "some " + m_variableName + " in " + m_spawn.m_splitFunction.toString();
	}
}
