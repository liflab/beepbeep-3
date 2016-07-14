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
package ca.uqac.lif.cep;

/**
 * A Pullable object that casts all its output to a given type.
 * @author Sylvain Hallé
 *
 * @param <T> The type of the output objects
 */
@SuppressWarnings("unchecked")
public class TypedPullable<T> implements Pullable
{
	/**
	 * The actual pullable this class is wrapping
	 */
	protected final Pullable m_pullable;
	
	public TypedPullable(Pullable p)
	{
		super();
		m_pullable = p;
	}

	@Override
	public T pull()
	{
		return (T) m_pullable.pull();
	}

	@Override
	public T pullHard()
	{
		return (T) m_pullable.pullHard();
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
