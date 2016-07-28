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
package ca.uqac.lif.cep.fol;

import java.util.Queue;

import ca.uqac.lif.cep.SingleProcessor;

public class InterpretationBuilder extends SingleProcessor 
{
	protected Interpretation m_interpretation;
	
	public InterpretationBuilder()
	{
		super(1, 1);
		m_interpretation = new Interpretation();
	}
	
	public InterpretationBuilder add(Predicate ... preds)
	{
		for (Predicate p : preds)
		{
			m_interpretation.addPredicate(p);
		}
		return this;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_interpretation.clear();
	}
	
	@Override
	public InterpretationBuilder clone()
	{
		InterpretationBuilder out = new InterpretationBuilder();
		out.setContext(m_context);
		out.m_interpretation = new Interpretation(m_interpretation);
		return out;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object o = inputs[0];
		if (o instanceof PredicateTuple)
		{
			m_interpretation.addPredicateTuple((PredicateTuple) o); 
		}
		return wrapObject(m_interpretation);
	}
	
}
