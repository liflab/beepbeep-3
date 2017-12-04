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
package ca.uqac.lif.cep.tmf;

import java.util.Queue;

import ca.uqac.lif.cep.SingleProcessor;

/**
 * Function processor that turns input events into the same
 * constant.
 * 
 * @author Sylvain Hallé
 */
@SuppressWarnings("squid:S2160")
public class ReplaceWith extends SingleProcessor
{
	/**
	 * The constant to return
	 */
	protected Object m_constant;

	public ReplaceWith(int in_arity, Object comp)
	{
		super(in_arity, 1);
		m_constant = comp;
	}
	
	public ReplaceWith(Object comp)
	{
		this(1, comp);
	}

	@Override
	public ReplaceWith duplicate()
	{
		ReplaceWith cp = new ReplaceWith(m_constant);
		cp.setContext(m_context);
		return cp;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		outputs.add(new Object[]{m_constant});
		return true;
	}
}
