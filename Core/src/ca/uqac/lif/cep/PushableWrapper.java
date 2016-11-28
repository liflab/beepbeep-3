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
 * Wrapper around an existing {@link Pushable} with delegate methods
 * @author Sylvain Hallé
 */
public class PushableWrapper implements Pushable
{
	protected Pushable m_pushable;
	
	public PushableWrapper(Pushable p)
	{
		super();
		m_pushable = p;
	}

	@Override
	public Pushable push(Object o)
	{
		return m_pushable.push(o);
	}

	@Override
	public Pushable pushFast(Object o)
	{
		return m_pushable.pushFast(o);
	}

	@Override
	public Processor getProcessor()
	{
		return m_pushable.getProcessor();
	}

	@Override
	public int getPosition()
	{
		return m_pushable.getPosition();
	}

	@Override
	public void waitFor()
	{
		m_pushable.waitFor();
	}

	@Override
	public void dispose()
	{
		m_pushable.dispose();
	}
}
