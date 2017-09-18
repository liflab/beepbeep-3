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
package ca.uqac.lif.cep;

import ca.uqac.lif.petitpoucet.DirectValue;
import ca.uqac.lif.petitpoucet.NodeFunction;

/**
 * Node function that relates to an event at a specific position,
 * in a specific stream of a specific processor.
 * @author Sylvain Hallé
 */
public abstract class EventFunction implements NodeFunction 
{
	/**
	 * The ID of the processor which produces the event
	 */
	protected int m_processorId; 
	
	/**
	 * The index of the output stream on the processor
	 */
	protected int m_streamIndex;
	
	/**
	 * The position in the stream where the event is
	 */
	protected int m_streamPosition;
	
	/**
	 * An instance of the {@link ca.uqac.lif.petitpoucet.DirectValue DirectValue}
	 * node function. All objects of this class have this as their final
	 * dependency, so we create only one instance and reuse it every time.
	 */
	protected static final transient DirectValue s_dependencyFunction = new DirectValue();
	
	/**
	 * Empty constructor. Only there to support deserialization with
	 * Azrael.
	 */
	protected EventFunction()
	{
		super();
	}
	
	/**
	 * Creates a new event function.
	 * @param id
	 * @param index
	 * @param position
	 */
	public EventFunction(int id, int index, int position)
	{
		super();
		m_processorId = id;
		m_streamIndex = index;
		m_streamPosition = position;
	}
	
	@Override
	public String toString()
	{
		return getDataPointId();
	}

	@Override
	public NodeFunction dependsOn() 
	{
		return s_dependencyFunction;
	}
	
	/**
	 * Gets the processor ID associated to this event function
	 * @return The ID
	 */
	public int getProcessorId()
	{
		return m_processorId;
	}
	
	/**
	 * Gets the stream index associated to this event function
	 * @return The index
	 */
	public int getStreamIndex()
	{
		return m_streamIndex;
	}
	
	/**
	 * Gets the stream position associated to this event function
	 * @return The position
	 */
	public int getStreamPosition()
	{
		return m_streamPosition;
	}
	
	public static class InputValue extends EventFunction
	{
		public InputValue(int id, int index, int position)
		{
			super(id, index, position);
		}
		
		@Override
		public String getDataPointId() 
		{
			return "BP" + m_processorId + ".I." + m_streamIndex + "." + m_streamPosition;
		}
	}
	
	public static class OutputValue extends EventFunction
	{
		public OutputValue(int id, int index, int position)
		{
			super(id, index, position);
		}
		
		@Override
		public String getDataPointId() 
		{
			return "BP" + m_processorId + ".O." + m_streamIndex + "." + m_streamPosition;
		}
	}
}
