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
package ca.uqac.lif.cep.functions;

import ca.uqac.lif.petitpoucet.NodeFunction;

/**
 * Creates a cumulative processor out of a cumulative function.
 * This is simply a {@link ApplyFunction} whose function is of
 * a specific type (a {@link CumulativeFunction}). However, it has a
 * special grammar that allows any binary function to be turned into
 * a cumulative processor.
 */
public class Cumulate extends ApplyFunction
{
	public Cumulate(CumulativeFunction<?> f)
	{
		super(f);
	}

	@Override
	protected boolean compute(Object[] inputs, Object[] outputs)
	{
		// We override compute() from FunctionProcessor, only to complete the
		// association between input and output events (each output event depends on
		// the current input event and also the previous output event front)
		boolean b = super.compute(inputs, outputs);
		if (m_eventTracker != null)
		{
			for (int j = 0; j < outputs.length; j++)
			{
				if (m_outputCount > 1)
				{
					for (int k = 0; k < outputs.length; k++)
					{
						// The output event is associated to the current input event
						// (this is already taken care of by super.compute)...
						// ...and to the previous output event
						// -1 and -2 since the count has already been incremented by the
						// call to super.compute() above
						associateToOutput(j, m_outputCount - 2, k, m_outputCount - 1);
						
					}
				}
				else
				{
					for (int k = 0; k < outputs.length; k++)
					{
						associateTo(new StartValue(getId(), j), k, m_outputCount - 1);
					}
				}
			}
		}
		return b;
	}

	/**
	 * Node function representing the start value defined for a particular
	 * function.
	 */
	public static class StartValue implements NodeFunction
	{
		/**
		 * The ID of the  processor this start value is associated
		 * with
		 */
		protected int m_processorId;

		/**
		 * In case the corresponding function is n-ary (with n &geq; 2),
		 * the index of the input stream
		 */
		protected int m_index;

		/**
		 * Empty constructor. Only there to support deserialization
		 * with Azrael.
		 */
		protected StartValue()
		{
			super();
		}

		/**
		 * Creates a new start value function
		 * @param id The ID of the processor this start value is associated
		 * with
		 * @param index The index of the input stream
		 */
		public StartValue(int id, int index) 
		{
			super();
			m_processorId = id;
		}

		/**
		 * Creates a new start value function
		 * @param id The ID of the processor this start value is associated
		 * with
		 */
		public StartValue(int id)
		{
			this(id, 0);
		}

		@Override
		public String toString()
		{
			return "Start value";
		}

		@Override
		public String getDataPointId() 
		{
			return "";
		}

		/**
		 * Gets the index of the input stream
		 * @return The index
		 */
		public int getStreamIndex()
		{
			return m_index;
		}

		@Override
		public NodeFunction dependsOn() 
		{
			// This is normal. This function is a leaf node in the dependency
			// tree, so its dependency is null.
			return null;
		}
	}
}
