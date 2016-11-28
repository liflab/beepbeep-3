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
 * Wrapper around an existing {@link Pullable} with delegate methods
 * @author Sylvain Hallé
 */
public class PullableWrapper implements Pullable
{
	protected Pullable m_pullable;
	
	public PullableWrapper(Pullable p)
	{
		super();
		m_pullable = p;
	}

	@Override
	public Object pullSoft() 
	{
		return m_pullable.pullSoft();
	}

	@Override
	public Object pull() 
	{
		return m_pullable.pull();
	}

	@Override
	public Object next() 
	{
		return m_pullable.next();
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
	public void dispose() 
	{
		m_pullable.dispose();
	}

	@Override
	public Iterator<Object> iterator() 
	{
		return m_pullable.iterator();
	}

	@Override
	public void remove() 
	{
		m_pullable.remove();
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

}
