package ca.uqac.lif.cep;

import ca.uqac.lif.petitpoucet.NodeFunction;

public class EventIndex implements NodeFunction 
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
	
	protected NodeFunction m_dependencyFunction;
	
	public EventIndex(int id, int index, int position, NodeFunction dependency)
	{
		super();
		m_processorId = id;
		m_streamIndex = index;
		m_streamPosition = position;
		m_dependencyFunction = dependency;
	}

	@Override
	public String getDataPointId() 
	{
		return "P" + m_processorId + ":" + m_streamIndex + "." + m_streamPosition;
	}

	@Override
	public NodeFunction dependsOn() 
	{
		return m_dependencyFunction;
	}
	
	public void setDependency(NodeFunction nf)
	{
		m_dependencyFunction = nf;
	}

}
