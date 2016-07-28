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
import java.util.Set;

/**
 * A context in which predicates can be evaluated.
 * <p>
 * An Interpretation implements the corresponding concept from first-order
 * logic. It defines sets of values, each associated with a name, called
 * the <em>domains</em>. It also defines a set of <em>predicates</em>, each.
 *  
 * @author Sylvain Hallé
 */
public class Interpretation
{
	/**
	 * The domains defined for this interpretation. The
	 * key of this map is the name of each domain, and the corresponding value
	 * is the set of values in this domain.
	 */
	protected Map<String,Set<Object>> m_domains;
	
	/**
	 * The predicates defined for this interpretation. The
	 * key of this map is the name of each predicate, and the value
	 * is the corresponding {@link Predicate} object.
	 */
	protected Map<String,Predicate> m_predicates;
	
	/**
	 * Creates a new empty interpretation
	 */
	public Interpretation()
	{
		super();
		m_domains = new HashMap<String,Set<Object>>();
		m_predicates = new HashMap<String,Predicate>();
	}
	
	/**
	 * Creates a new interpretation
	 * @param domains The domains defined for this interpretation. The
	 * key of this map is the name of each domain, and the corresponding value
	 * is the set of values in this domain. 
	 * @param predicates The predicates defined for this interpretation. The
	 * key of this map is the name of each predicate, and the value
	 * is the corresponding {@link Predicate} object.
	 */
	public Interpretation(Map<String,Set<Object>> domains, Map<String,Predicate> predicates)
	{
		super();
		m_domains = domains;
		m_predicates = predicates;
	}
	
	/**
	 * Creates a copy of an interpretation
	 * @param inter The interpretation to copy
	 */
	public Interpretation(Interpretation inter)
	{
		super();
		for (String domain_name : inter.m_domains.keySet())
		{
			HashSet<Object> values = new HashSet<Object>();
			values.addAll(inter.m_domains.get(domain_name));
			m_domains.put(domain_name, values);
		}
		for (String pred_name : inter.m_predicates.keySet())
		{
			Predicate new_p = new Predicate(inter.m_predicates.get(pred_name));
			m_predicates.put(pred_name, new_p);
		}
	}
	
	/**
	 * Gets the set of values of the given domain
	 * @param domain_name The name of the domain
	 * @return The set of values. An empty set is returned if no
	 *   domain with given name exists, or if
	 *   <code>domain_name</code> is null.
	 */
	public Set<Object> getDomain(/*@Null*/ String domain_name)
	{
		if (domain_name == null || !m_domains.containsKey(domain_name))
		{
			return new HashSet<Object>();
		}
		return m_domains.get(domain_name);
	}
	
	/**
	 * Adds a new value to a domain
	 * @param domain_name The name of the domain
	 * @param value The value to add
	 */
	public void addToDomain(String domain_name, Object value)
	{
		Set<Object> values = null;
		if (!m_domains.containsKey(domain_name))
		{
			values = new HashSet<Object>();
		}
		else
		{
			values = m_domains.get(domain_name);
		}
		values.add(value);
		m_domains.put(domain_name, values);
	}
	
	/**
	 * Adds a new predicate tuple to the definition of some predicate.
	 * This also updates the domains
	 * @param tuple The tuple to add
	 */
	public void addPredicateTuple(PredicateTuple tuple)
	{
		if (m_predicates.containsKey(tuple.m_name))
		{
			Predicate pred = m_predicates.get(tuple.m_name);
			pred.m_definition.put(tuple.m_arguments, tuple.m_value);
			for (int i = 0; i < pred.m_domainNames.length; i++)
			{
				addToDomain(pred.m_domainNames[i], tuple.m_arguments.m_values[i]);
			}
		}
	}
	
	public void addPredicate(Predicate p)
	{
		m_predicates.put(p.m_name, p);
		for (String domain_name : p.m_domainNames)
		{
			if (!m_domains.containsKey(domain_name))
			{
				m_domains.put(domain_name, new HashSet<Object>());
			}
		}
	}
	
	public void clear()
	{
		for (String predicate_name : m_predicates.keySet())
		{
			// Clear predicates
			m_predicates.get(predicate_name).clear();
		}
		for (String domain_name : m_domains.keySet())
		{
			// Clear domains
			m_domains.put(domain_name, new HashSet<Object>());
		}
	}
}