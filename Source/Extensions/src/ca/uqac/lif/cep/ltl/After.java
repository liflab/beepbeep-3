package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ltl.Troolean.Value;

public class After extends UnaryProcessor 
{
	private int m_eventCount = 0;
	
	private Value m_valueToReturn = Value.INCONCLUSIVE;

	@Override
	protected Object computeInternal(Value o) 
	{
		if (m_eventCount == 0)
		{
			m_eventCount = 1;
			return Value.INCONCLUSIVE;
		}
		else if (m_eventCount == 1)
		{
			m_eventCount = 2;
			m_valueToReturn = o;
		}
		return m_valueToReturn;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_valueToReturn = Value.INCONCLUSIVE;
		m_eventCount = 0;
	}

	@Override
	public Processor clone() 
	{
		return new After();
	}

}
