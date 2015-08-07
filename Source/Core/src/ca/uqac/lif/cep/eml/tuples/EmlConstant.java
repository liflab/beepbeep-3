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
package ca.uqac.lif.cep.eml.tuples;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Vector;

public abstract class EmlConstant extends Tuple
{
	public EmlConstant()
	{
		super();
	}
	
	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		Queue<Vector<Object>> out = new LinkedList<Vector<Object>>();
		Vector<Object> element = new Vector<Object>();
		element.addElement(this);
		out.add(element);
		return out;
	}
	
	/**
	 * Attempts to create a constant based on the contents of a string.
	 * That is, if the string contains only digits, it will create an
	 * {@link EmlNumber} instead of an {@link EmlString}.
	 * @param s The string to read from
	 * @return The constant
	 */
	public static EmlConstant createConstantFromString(String s)
	{
		int n = 0;
		try
		{
			n = Integer.parseInt(s);
		}
		catch (NumberFormatException nfe)
		{
			// This is a string
			return new EmlString(s);
		}
		return new EmlNumber(n);
	}
	
	@Override
	public EmlConstant newInstance()
	{
		EmlConstant out = null;
		Class<?> c = this.getClass();
		try {
			out = (EmlConstant) c.newInstance();
		} catch (InstantiationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IllegalAccessException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return out;
	}
}
