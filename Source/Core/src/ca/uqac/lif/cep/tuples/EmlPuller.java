/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

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
package ca.uqac.lif.cep.tuples;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;

/**
 * Provides a wrapper to the original {@link Pullable} interface,
 * with methods for casting the result into various types. This is
 * merely for convenience.
 * 
 * @author Sylvain Hallé
 *
 */
public class EmlPuller
{
	/**
	 * Get an EmlPuller from a processor. 
	 * @param p The processor
	 * @param i The index of the pullable to get
	 * @return The pullable, or null if none could be given
	 */
	public static EmlPullable getEmlPullable(Processor p, int i)
	{
		if (p == null)
		{
			return null;
		}
		Pullable pul = p.getPullableOutput(i);
		if (pul == null)
		{
			return null;
		}
		return new EmlPullable(pul);
	}
	
	public static EmlPullable getEmlPullable(Processor p)
	{
		return getEmlPullable(p, 0);
	}
	
	/**
	 * A wrapper to the original {@link Pullable} interface,
   * with methods for casting the result into various types.
	 * @author Sylvain Hallé
	 *
	 */
	public static class EmlPullable implements Pullable
	{
		/**
		 * The pullable to wrap
		 */
		private final Pullable m_pullable;
		
		public EmlPullable(Pullable p)
		{
			super();
			m_pullable = p;
		}

		@Override
		public Object pull()
		{
			return m_pullable.pull();
		}
		
		public float pullFloat()
		{
			return EmlNumber.parseFloat(m_pullable.pull());
		}
		
		public int pullInt()
		{
			return (int) pullFloat();
		}
		
		public String pullString()
		{
			return EmlString.parseString(m_pullable.pull());
		}
		
		public Tuple pullTuple()
		{
			return (Tuple) m_pullable.pull();
		}
		
		public NamedTuple pullNamedTuple()
		{
			return (NamedTuple) m_pullable.pull();
		}

		@Override
		public Object pullHard()
		{
			return m_pullable.pullHard();
		}

		@Override
		public NextStatus hasNext()
		{
			return m_pullable.hasNext();
		}

		@Override
		public NextStatus hasNextHard()
		{
			return m_pullable.hasNextHard();
		}

		@Override
		public int getPullCount()
		{
			return m_pullable.getPullCount();
		}

		@Override
		public Processor getProcessor()
		{
			return m_pullable.getProcessor();
		}

		@Override
		public int getPosition() 
		{
			return m_pullable.getPosition();
		}
	}
}
