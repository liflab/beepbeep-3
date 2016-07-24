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
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.GroupProcessor;
import ca.uqac.lif.cep.Passthrough;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.SimpleFunction;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public abstract class TrooleanQuantifier extends GroupProcessor 
{
	protected String m_variableName;
	
	protected SentinelIn m_sentinelIn;
	
	protected FirstOrderSpawn m_spawn;
	
	protected SentinelOut m_sentinelOut;
	
	protected Troolean.Value m_valueIfEmptyDomain;
	
	TrooleanQuantifier()
	{
		super(1, 1);
		m_valueIfEmptyDomain = Troolean.Value.TRUE;
	}
	
	public TrooleanQuantifier(String var_name, Function split_function, Processor p, Function combine_function, Object value_empty)
	{
		super(1, 1);
		m_valueIfEmptyDomain = Troolean.Value.TRUE;
		m_sentinelIn = new SentinelIn();
		addProcessor(m_sentinelIn);
		m_spawn = new FirstOrderSpawn(var_name, split_function, p, combine_function, value_empty);
		addProcessor(m_spawn);
		m_sentinelOut = new SentinelOut();
		addProcessor(m_sentinelOut);
		try 
		{
			Connector.connect(m_sentinelIn, m_spawn);
			Connector.connect(m_spawn, m_sentinelOut);
		} 
		catch (ConnectorException e) 
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		associateInput(0, m_sentinelIn, 0);
		associateOutput(0, m_sentinelOut, 0);
	}
	
	public Map<Integer,Processor> cloneInto(TrooleanQuantifier q)
	{
		Map<Integer,Processor> map = super.cloneInto(q);
		q.m_sentinelIn = (SentinelIn) map.get(m_sentinelIn.getId());
		q.m_sentinelOut = (SentinelOut) map.get(m_sentinelOut.getId());
		q.m_spawn = (FirstOrderSpawn) map.get(m_spawn.getId());
		q.m_variableName = m_variableName;
		try 
		{
			Connector.connect(q.m_sentinelIn, q.m_spawn);
			Connector.connect(q.m_spawn, q.m_sentinelOut);
		} 
		catch (ConnectorException e) 
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		q.associateInput(0, q.m_sentinelIn, 0);
		q.associateOutput(0, q.m_sentinelOut, 0);
		return map;
	}
	
	protected class FirstOrderSpawn extends Spawn
	{
		public FirstOrderSpawn(String var_name, Function split_function, Processor p, Function combine_function, Object value_empty)
		{
			super(p, split_function, combine_function);
			m_variableName = var_name;
			m_valueIfEmptyDomain = value_empty;
			//m_domainFunction = domain;
		}

		@Override
		public void addContextFromSlice(Processor p, Object slice) 
		{
			Object[] input = new Object[1];
			input[0] = slice;
			p.setContext(m_variableName, slice);
		}

		@Override
		public FirstOrderSpawn clone()
		{
			return new FirstOrderSpawn(m_variableName, m_splitFunction.clone(m_context), m_processor.clone(), m_combineProcessor.getFunction().clone(m_context), m_valueIfEmptyDomain);
		}
	}
	
	protected class SentinelIn extends Passthrough
	{
		public SentinelIn()
		{
			super(1);
		}

		@Override
		public SentinelIn clone() 
		{
			return new SentinelIn();
		}
	}
	
	protected class SentinelOut extends SingleProcessor
	{
		protected Troolean.Value m_definiteValue = Value.INCONCLUSIVE;
		
		public SentinelOut()
		{
			super(1, 1);
		}

		@Override
		protected Queue<Object[]> compute(Object[] inputs)
		{
			if (m_definiteValue != Value.INCONCLUSIVE)
			{
				return wrapObject(m_definiteValue);
			}
			if (inputs[0] instanceof Troolean.Value && ((Troolean.Value) inputs[0]) != Value.INCONCLUSIVE)
			{
				m_definiteValue = (Troolean.Value) inputs[0];
				// Bypass the first-order quantifier once a definite
				// value was obtained. This is done by repiping the "in" sentinel
				// directly to the "out" sentinel
				try 
				{
					Connector.connect(m_sentinelIn, this);
				} 
				catch (ConnectorException e) 
				{
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				return wrapObject(m_definiteValue);
			}
			return new ArrayDeque<Object[]>();
		}

		@Override
		public SentinelOut clone() 
		{
			return new SentinelOut();
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
