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

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.CumulativeFunction;
import ca.uqac.lif.cep.CumulativeProcessor;
import ca.uqac.lif.cep.Function;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.epl.Slicer;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public abstract class FirstOrderSlicer extends GroupProcessor
{
	FirstOrderSlicer(Function slicing_function, Processor p) throws ConnectorException
	{
		super(1, 1);
		Slicer slicer = new Slicer(slicing_function, p);
		CumulativeProcessor merge = new CumulativeProcessor(getMergeFunction());
		Connector.connect(slicer, merge);
		addProcessors(slicer, merge);
	}
	
	protected abstract CumulativeFunction<Value> getMergeFunction(); 
}
