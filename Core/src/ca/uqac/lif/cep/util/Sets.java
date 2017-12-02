/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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
package ca.uqac.lif.cep.util;

import java.util.HashSet;
import java.util.Set;

import ca.uqac.lif.cep.UniformProcessor;
import ca.uqac.lif.cep.functions.BinaryFunction;

/**
 * A container object for set functions and processors.
 * Some functions come in two flavors:
 * <ul>
 * <li>The "plain" function takes as input a set object and returns the
 * <em>same</em> object</li>, to which a modification has been applied
 * <li>The "new" function takes as input a set object, and returns a
 * <em>new copy</em> of the object with the modification made to it</li>
 * </ul>
 * @author Sylvain Hallé
 */
public class Sets
{
	private Sets()
	{
		// Utility class
	}
	
	public static final IsSubsetOrEqual isSubsetOrEqual = new IsSubsetOrEqual(); 
	
	/**
	 * Processor that updates a set
	 */
	protected abstract static class SetUpdateProcessor extends UniformProcessor
	{
		/**
		 * The underlying set
		 */
		protected Set<Object> m_set;
		
		/**
		 * Create a new instance of the processor
		 */
		public SetUpdateProcessor()
		{
			super(1, 1);
			m_set = new HashSet<Object>();
		}
		
		@Override
		public void reset()
		{
			m_set.clear();
		}
		
		@Override
		public Class<?> getOutputType(int index)
		{
			return Set.class;
		}
	}
		
	/**
	 * Updates a set.
	 */
	public static class PutInto extends SetUpdateProcessor
	{	
		/**
		 * Create a new instance of the processor
		 */
		public PutInto()
		{
			super();
		}

		@Override
		public PutInto duplicate()
		{
			return new PutInto();
		}

		@Override
		protected boolean compute(Object[] inputs, Object[] outputs) 
		{
			m_set.add(inputs[0]);
			outputs[0] = m_set;
			return true;
		}
	}
	
	/**
	 * Updates a set.
	 */
	public static class PutIntoNew extends SetUpdateProcessor
	{	
		/**
		 * Create a new instance of the processor
		 */
		public PutIntoNew()
		{
			super();
		}

		@Override
		public PutIntoNew duplicate()
		{
			return new PutIntoNew();
		}

		@Override
		protected boolean compute(Object[] inputs, Object[] outputs) 
		{
			m_set.add(inputs[0]);
			HashSet<Object> new_set = new HashSet<Object>();
			new_set.addAll(m_set);
			outputs[0] = new_set;
			return true;
		}
	}
	
	/**
	 * Checks if a set is a subset of another. The first argument is the set
	 * to check, and the second argument is the reference set.
	 */
	@SuppressWarnings("rawtypes")
	public static class IsSubsetOrEqual extends BinaryFunction<Set,Set,Boolean>
	{
		protected IsSubsetOrEqual()
		{
			super(Set.class, Set.class, Boolean.class);
		}

		@SuppressWarnings("unchecked")
		@Override
		public Boolean getValue(Set x, Set y)
		{
			return y.containsAll(x);
		}
	}
}
