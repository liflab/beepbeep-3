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
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.epl.Slicer;
import ca.uqac.lif.cep.functions.CumulativeFunction;
import ca.uqac.lif.cep.functions.CumulativeProcessor;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public abstract class FirstOrderSlicer extends GroupProcessor
{
	protected String m_variableName;
	
	FirstOrderSlicer(String variable_name, Function slicing_function, Processor p) throws ConnectorException
	{
		super(1, 1);
		m_variableName = variable_name;
		ContextSlicer slicer = new ContextSlicer(slicing_function, p);
		CumulativeProcessor merge = new CumulativeProcessor(getMergeFunction());
		Connector.connect(slicer, merge);
		addProcessors(slicer, merge);
		associateInput(0, slicer, 0);
		associateOutput(0, merge, 0);
	}
	
	FirstOrderSlicer(Function slicing_function, Processor p) throws ConnectorException
	{
		this(null, slicing_function, p);
	}
	
	protected abstract CumulativeFunction<Value> getMergeFunction();
	
	protected class ContextSlicer extends Slicer
	{
		public ContextSlicer(Function func, Processor proc) 
		{
			super(func, proc);
		}
		
		@Override
		public void addContextFromSlice(Processor p, Object slice)
		{
			if (m_variableName != null)
			{
				p.setContext(m_variableName, slice);
			}
		}
		
		@Override
		public ContextSlicer clone()
		{
			return new ContextSlicer(getMergeFunction(), m_processor);
		}
		
	}
}
