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
package ca.uqac.lif.cep.fsm;

import java.util.ArrayList;
import java.util.List;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.fsm.MooreMachine.Transition;
import ca.uqac.lif.cep.functions.ContextAssignment;
import ca.uqac.lif.cep.functions.Function;

/**
 * Transition for a Moore Machine where the guard is a function
 * returning a <code>boolean</code>, and the context modification
 * is a list of {@link ca.uqac.lif.cep.functions.ContextAssignment}s.
 * 
 * @author Sylvain Hallé
 */
public class FunctionTransition extends Transition
{
	protected Function m_function;
	
	protected List<ContextAssignment> m_assignments;

	protected int m_destination = -1;
	
	public FunctionTransition(FunctionTransition t)
	{
		this(t.m_function, t.m_destination);
	}
	
	public FunctionTransition(Function function, int destination, ContextAssignment asg)
	{
		super();
		m_function = function;
		m_destination = destination;
		m_assignments = new ArrayList<ContextAssignment>();
		m_assignments.add(asg);
	}
	
	public FunctionTransition(Function function, int destination, ContextAssignment ... asgs)
	{
		super();
		m_function = function;
		m_destination = destination;
		m_assignments = new ArrayList<ContextAssignment>();
		for (ContextAssignment asg : asgs)
		{
			m_assignments.add(asg);
		}
	}
	
	public FunctionTransition(Function function, int destination)
	{
		super();
		m_function = function;
		m_destination = destination;
		m_assignments = new ArrayList<ContextAssignment>();
	}

	@Override
	public boolean isFired(Object[] input, Context context)
	{
		Object[] values = m_function.evaluate(input, context);
		boolean b = (boolean) values[0];
		return b;
	}

	@Override
	public int getDestination()
	{
		return m_destination;
	}
	
	@Override
	public void modifyContext(Object[] inputs, MooreMachine machine)
	{
		for (ContextAssignment asg : m_assignments)
		{
			asg.assign(inputs, machine);
		}
	}
	
	@Override
	public FunctionTransition clone()
	{
		FunctionTransition out = new FunctionTransition(m_function, m_destination);
		out.m_assignments.addAll(m_assignments);
		return out;
	}
	
	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append(m_function).append(" -> ").append(m_destination);
		if (!m_assignments.isEmpty())
		{
			out.append(" / ").append(m_assignments);
		}
		return out.toString();
	}
}