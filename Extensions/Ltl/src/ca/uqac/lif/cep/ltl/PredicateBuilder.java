package ca.uqac.lif.cep.ltl;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.ltl.Predicate.PredicateTuple;

public class PredicateBuilder extends SingleProcessor 
{
	protected Map<String,Predicate> m_predicates;
	
	protected Set<String> m_domainNames;
	
	public PredicateBuilder()
	{
		super(1, 1);
		m_predicates = new HashMap<String,Predicate>();
		m_domainNames = new HashSet<String>();
	}
	
	public PredicateBuilder add(Predicate ... preds)
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
	public PredicateBuilder clone()
	{
		PredicateBuilder out = new PredicateBuilder();
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
		Map<String,Set<Object>> domain_defs = new HashMap<String,Set<Object>>();
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
		return wrapObject(inter);
	}
	
}
