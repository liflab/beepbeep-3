package ca.uqac.lif.cep.ltl;

import java.util.Queue;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.ltl.Troolean.Value;

/**
 * Troolean implementation of the LTL <b>X</b> operator
 * @author Sylvain Hallé
 */
public class After extends SingleProcessor 
{
	/**
	 * The number of events received so far
	 */
	private int m_eventCount = 0;
	
	/**
	 * The value to return (so far)
	 */
	private Value m_valueToReturn = Value.INCONCLUSIVE;
	
	public After()
	{
		super(1, 1);
	}

	@Override
	protected Queue<Object[]> compute(Object[] input) 
	{
		if (m_eventCount == 0)
		{
			m_eventCount = 1;
			return wrapObject(Value.INCONCLUSIVE);
		}
		else if (m_eventCount == 1)
		{
			m_eventCount = 2;
			m_valueToReturn = Troolean.trooleanValue(input[0]);
		}
		return wrapObject(m_valueToReturn);
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
