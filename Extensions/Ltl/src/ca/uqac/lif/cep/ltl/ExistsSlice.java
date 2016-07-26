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

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public class ExistsSlice extends FirstOrderSlicer
{
	public ExistsSlice(String variable_name, Function slice_function, Processor p) throws ConnectorException 
	{
		super(slice_function, p);
	}
	
	public ExistsSlice(Function slice_function, Processor p) throws ConnectorException 
	{
		super(slice_function, p);
	}

	@Override
	protected CumulativeFunction<Value> getMergeFunction()
	{
		return new CumulativeFunction<Value>(Troolean.OR_FUNCTION);
	}
}