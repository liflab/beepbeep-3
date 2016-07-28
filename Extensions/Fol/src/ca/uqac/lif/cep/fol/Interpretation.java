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
}