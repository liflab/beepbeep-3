package ca.uqac.lif.cep.io;

import java.util.Queue;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;

public class LineTokenFeeder extends SingleProcessor
{
	StringBuilder m_currentEvent;

	protected String m_startToken;

	protected String m_endToken;

	protected int m_tokensFed = 0;

	protected boolean m_printStatus = false;

	public LineTokenFeeder(String start_token, String end_token)
	{
		super(1, 1);
		m_currentEvent = new StringBuilder();
		m_startToken = start_token;
		m_endToken = end_token;
	}
	
	/**
	 * Sets whether the feeder prints a status line
	 * @param b Set to <code>true</code> to print a status line
	 */
	public void printStatus(boolean b)
	{
		m_printStatus = b;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		String line = ((String) inputs[0]).trim();
		if (line.compareTo(m_startToken) == 0)
		{
			m_currentEvent = new StringBuilder();
			m_currentEvent.append(line).append("\n");
			return Processor.getEmptyQueue();
		}
		if (line.compareTo(m_endToken) == 0)
		{
			m_currentEvent.append(line);
			if (m_printStatus)
			{
				m_tokensFed++;
				if (m_tokensFed % 1000 == 0)
				{
					System.out.println("Tokens fed: " + m_tokensFed);
				}
			}
			return wrapObject(m_currentEvent.toString());
		}
		m_currentEvent.append(line);
		return Processor.getEmptyQueue();
	}

	@Override
	public LineTokenFeeder clone()
	{
		LineTokenFeeder ltf = new LineTokenFeeder(m_startToken, m_endToken);
		ltf.setContext(m_context);
		return ltf;
	}
}
