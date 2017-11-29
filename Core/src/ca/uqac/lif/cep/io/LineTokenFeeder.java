package ca.uqac.lif.cep.io;

import java.util.Queue;

import ca.uqac.lif.cep.SingleProcessor;

@SuppressWarnings("squid:S2160")
public class LineTokenFeeder extends SingleProcessor
{
	/**
	 * 
	 */
	private static final long serialVersionUID = 230382528486632578L;

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
	@SuppressWarnings({"squid:S106", "squid:S3516"}) 
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		String line = ((String) inputs[0]).trim();
		if (line.compareTo(m_startToken) == 0)
		{
			m_currentEvent = new StringBuilder();
			m_currentEvent.append(line).append("\n");
			return true;
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
			outputs.add(wrapObject(m_currentEvent.toString()));
			return true;
		}
		m_currentEvent.append(line);
		return true;
	}

	@Override
	public LineTokenFeeder duplicate()
	{
		LineTokenFeeder ltf = new LineTokenFeeder(m_startToken, m_endToken);
		ltf.setContext(m_context);
		return ltf;
	}
}
