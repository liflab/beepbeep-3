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
package ca.uqac.lif.cep.interpreter;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

class GroupStack<T> extends Stack<T>
{
	/**
	 * Dummy UID
	 */
	private static final long serialVersionUID = 1L;

	protected Set<T> m_parsedObjects;

	public GroupStack()
	{
		super();
		m_parsedObjects = new HashSet<T>();
	}

	@Override
	public T push(T o)
	{
		m_parsedObjects.add(o);
		return super.push(o);
	}

	public Set<T> getHistory()
	{
		return m_parsedObjects;
	}

	@Override
	public void clear()
	{
		super.clear();
		m_parsedObjects.clear();
	}

}