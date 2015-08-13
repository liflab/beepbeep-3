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
package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.eml.tuples.EmlBoolean;

public class Next extends UnaryProcessor 
{
	protected short m_eventCount;
	
	protected EmlBoolean m_verdict;
	
	public Next()
	{
		super();
		m_eventCount = 0;
		m_verdict = null;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_eventCount = 0;
		m_verdict = null;
	}

	@Override
	protected EmlBoolean compute(EmlBoolean input)
	{
		if (m_verdict != null)
		{
			return m_verdict;
		}
		m_eventCount++;
		if (m_eventCount == 1)
		{
			return null;
		}
		if (m_eventCount == 2)
		{
			m_verdict = input;
			return input;
		}
		return null;
	}
}
