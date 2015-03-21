/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep.input;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Vector;

import ca.uqac.lif.cep.SingleProcessor;

public abstract class TokenFeeder extends SingleProcessor
{
	protected StringBuilder m_bufferedContents;

	protected String m_separatorBegin;
	protected String m_separatorEnd;

	public TokenFeeder()
	{
		super(1, 1);
		m_bufferedContents = new StringBuilder();
	}

	protected abstract Object createTokenFromInput(String token);

	/**
	 * Analyzes the current contents of the buffer; extracts a complete token
	 * from it, if any is present
	 * @param to_fill Will be filled with the contents of the next token
	 */
	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		for (Object o : inputs)
		{
			if (o instanceof String)
			{
				String s = (String) o;
				m_bufferedContents.append(s);
			}
		}
		Queue<Vector<Object>> out = new LinkedList<Vector<Object>>();
		String s = m_bufferedContents.toString();
		while (!s.isEmpty())
		{
			int index = s.indexOf(m_separatorEnd);
			if (index < 0)
			{
				return out;
			}
			int index2 = s.indexOf(m_separatorBegin);
			if (index2 > index)
				index2 = 0;
			if (index2 < 0)
				break;
			String s_out = s.substring(index2, index + m_separatorEnd.length());
			//m_bufferedContents.delete(index2, index + m_separatorEnd.length());
			m_bufferedContents.delete(0, index + m_separatorEnd.length());
			Object token = createTokenFromInput(s_out);
			if (token != null)
			{
				Vector<Object> to_fill = new Vector<Object>();
				to_fill.add(token);
				out.add(to_fill);
			}
			else
			{
				break;
			}
			s = m_bufferedContents.toString();
		}
		return out;
	}

}
