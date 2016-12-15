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

import java.util.Iterator;

/**
 * A Pullable object that casts all its output to a given type.
 * The TypedPullable is used by wrapping it around an existing
 * pullable:
 * <pre>
 * ...
 * Pullable p = my_processor.getPullableOutput(0);
 * TypedPullable&lt;Integer&gt; tp = new TypedPullable&lt;Integer&gt;(p);
 * int event = tp.pull();
 * </pre>
 * <strong>Caveat emptor:</strong> This pullable simply <em>casts</em>
 * what it receives from its underlying pullable to the type it was
 * created with. It is up to the user to make sure that this cast
 * makes sense; otherwise, a <tt>ClassCastException</tt> will be thrown
 * at runtime.
 * 
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
	public void remove()
	{
		// Cannot remove an event on a pullable
		throw new UnsupportedOperationException();
	}

	@Override
	public T pullSoft()
	{
		return (T) m_pullable.pullSoft();
	}

	@Override
	public T pull()
	{
		return (T) m_pullable.pull();
	}

	@Override
	public final T next()
	{
		return pull();
	}

	@Override
	public NextStatus hasNextSoft()
	{
		return m_pullable.hasNextSoft();
	}

	@Override
	public boolean hasNext()
	{
		return m_pullable.hasNext();
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

	@Override
	public Iterator<Object> iterator()
	{
		return this;
	}

	@Override
	public void start()
	{
		m_pullable.start();
	}

	@Override
	public void stop()
	{
		m_pullable.stop();
	}

	@Override
	public void dispose()
	{
		// Do nothing
	}
}
