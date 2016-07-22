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

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Set;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.SimpleFunction;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public abstract class FirstOrderQuantifier extends GroupProcessor 
{
	protected String m_variableName;
	
	protected FirstOrderSpawn m_spawn;
	
	public FirstOrderQuantifier(String var_name, Function split_function, Processor p, Function combine_function)
	{
		super(1, 1);
		m_spawn = new FirstOrderSpawn(var_name, split_function, p, combine_function);
		addProcessor(m_spawn);
		SentinelPassthrough spt = new SentinelPassthrough();
		addProcessor(spt);
		try 
		{
			Connector.connect(m_spawn, spt);
		} 
		catch (ConnectorException e) 
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		associateInput(0, m_spawn, 0);
		associateOutput(0, spt, 0);
	}
	
	protected class FirstOrderSpawn extends Spawn
	{
		public FirstOrderSpawn(String var_name, Function split_function, Processor p, Function combine_function)
		{
			super(p, split_function, combine_function);
			m_variableName = var_name;
			//m_domainFunction = domain;
		}

		@Override
		public void addContextFromSlice(Processor p, Object slice) 
		{
			Object[] input = new Object[1];
			input[0] = slice;
			p.setContext(m_variableName, slice);
		}
	}
	
	protected class SentinelPassthrough extends SingleProcessor
	{
		protected Troolean.Value m_definiteValue = Value.INCONCLUSIVE;
		
		public SentinelPassthrough()
		{
			super(1, 1);
		}

		@Override
		protected Queue<Object[]> compute(Object[] inputs)
		{
			if (m_definiteValue == Value.INCONCLUSIVE && ((Troolean.Value) inputs[0]) != Value.INCONCLUSIVE)
			{
				m_definiteValue = (Troolean.Value) inputs[0];
			}
			if (m_definiteValue != Value.INCONCLUSIVE)
			{
				return wrapObject(m_definiteValue);
			}
			return new ArrayDeque<Object[]>();
		}

		@Override
		public SentinelPassthrough clone() 
		{
			return new SentinelPassthrough();
		}
	}
	
	public static abstract class ArrayTroolean extends SimpleFunction
	{
		@Override
		public int getInputArity() 
		{
			return 1;
		}

		@Override
		public int getOutputArity()
		{
			return 1;
		}

		@Override
		public void reset()
		{
			// Nothing to do
		}

		@Override
		public void getInputTypesFor(Set<Class<?>> classes, int index)
		{
			classes.add(Troolean.Value.class);
		}

		@Override
		public Class<?> getOutputTypeFor(int index)
		{
			return Troolean.Value.class;
		}
	}

}
