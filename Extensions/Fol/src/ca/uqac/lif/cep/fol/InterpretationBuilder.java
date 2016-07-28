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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import ca.uqac.lif.cep.SingleProcessor;

public class InterpretationBuilder extends SingleProcessor 
{
	protected Map<String,Predicate> m_predicates;
	
	protected Set<String> m_domainNames;
	
	protected Interpretation m_interpretation;
	
	public InterpretationBuilder()
	{
		super(1, 1);
		m_predicates = new HashMap<String,Predicate>();
		m_domainNames = new HashSet<String>();
		m_interpretation = new Interpretation();
	}
	
	public InterpretationBuilder add(Predicate ... preds)
	{
		for (Predicate p : preds)
		{
			m_predicates.put(p.m_name, p);
			m_domainNames.addAll(p.getDomainNames());
		}
		return this;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_predicates.clear();
	}
	
	@Override
	public InterpretationBuilder clone()
	{
		InterpretationBuilder out = new InterpretationBuilder();
		out.setContext(m_context);
		for (String name : m_predicates.keySet())
		{
			Predicate new_p = m_predicates.get(name).clone(m_context);
			out.m_predicates.put(name, new_p);
		}
		return out;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		Object o = inputs[0];
		if (o instanceof PredicateTuple)
		{
			PredicateTuple tuple = (PredicateTuple) o;
			String pred_name = tuple.m_name;
			if (m_predicates.containsKey(pred_name))
			{
				Predicate pred = m_predicates.get(pred_name);
				pred.updateDefinition(tuple);
			}
		}
		return wrapObject(m_interpretation);
		/*Map<String,Set<Object>> domain_defs = new HashMap<String,Set<Object>>();
		for (String domain_name : m_domainNames)
		{
			Set<Object> domain = new HashSet<Object>();
			for (Predicate pred : m_predicates.values())
			{
				domain.addAll(pred.getValuesForDomain(domain_name));
			}
			domain_defs.put(domain_name, domain);
		}
		Interpretation inter = new Interpretation(domain_defs, m_predicates);
		return wrapObject(inter);*/
	}
	
}
