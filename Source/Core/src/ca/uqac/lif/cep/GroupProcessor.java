/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import ca.uqac.lif.bullwinkle.BnfRule;

/**
 * Encapsulates a chain of processors as if it were a single one.
 * 
 * @author Sylvain Hallé
 */
public class GroupProcessor extends Processor
{
	/**
	 * The set of processors included in the group
	 */
	protected Set<Processor> m_processors = null;

	/**
	 * The {@link Pushable}s associated to each of the processor's
	 * input traces
	 */
	protected Vector<Pushable> m_inputPushables = null;

	/**
	 * The {@link Pullable}s associated to each of the processor's
	 * output traces
	 */
	protected Vector<Pullable> m_outputPullables = null;
	
	/**
	 * A map between numbers and processor associations. An element
	 * (m,(n,p)) of this map means that the <i>m</i>-th input of the
	 * group processor is in fact the <i>n</i>-th input of processor
	 * <code>p</code>
	 */
	protected Map<Integer,ProcessorAssociation> m_inputPullableAssociations;

	/**
	 * A map between numbers and processor associations. An element
	 * (m,(n,p)) of this map means that the <i>m</i>-th output of the
	 * group processor is in fact the <i>n</i>-th output of processor
	 * <code>p</code>
	 */
	protected Map<Integer,ProcessorAssociation> m_outputPushableAssociations;
	
	/**
	 * If this group processor is associated to a BNF rule, this contains
	 * the name of the non-terminal part (left-hand side) of the rule
	 */
	protected String m_ruleName;

	/**
	 * If this group processor is associated to a BNF rule, this contains
	 * the name right-hand side of the rule
	 */
	protected BnfRule m_rule;

	/**
	 * Crate a group processor
	 * @param in_arity The input arity
	 * @param out_arity The output arity
	 */
	public GroupProcessor(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
		m_processors = new HashSet<Processor>();
		m_inputPushables = new Vector<Pushable>();
		m_outputPullables = new Vector<Pullable>();
		m_inputPullableAssociations = new HashMap<Integer,ProcessorAssociation>();
		m_outputPushableAssociations = new HashMap<Integer,ProcessorAssociation>();
	}
	
	/**
	 * Sets the name of the rule associated to this processor
	 * @param rule_name The rule name
	 */
	public void setRuleName(String rule_name)
	{
		m_ruleName = rule_name;
	}
	
	/**
	 * Retrieves the name of the rule associated to this processor
	 * @return The rule name
	 */
	public String getRuleName()
	{
		return m_ruleName;
	}
	
	/**
	 * Retrieves the BNF parsing rule associated to this group processor
	 * @return The parsing rule
	 */
	public BnfRule getRule()
	{
		return m_rule;
	}
	
	/**
	 * Tuple made of a number and a processor.
	 * 
	 * @author Sylvain Hallé
	 */
	protected static class ProcessorAssociation
	{
		/**
		 * The number
		 */
		int m_outputNumber;
		
		/**
		 * The processor
		 */
		Processor m_processor;
		
		/**
		 * Create a new processor association
		 * @param number The number
		 * @param p The processor associated to that number
		 */
		ProcessorAssociation(int number, Processor p)
		{
			m_outputNumber = number;
			m_processor = p;
		}
	}

	@Override
	public void reset()
	{
		// Reset all processors inside the group
		if (m_processors != null)
		{
			for (Processor p : m_processors)
			{
				p.reset();
			}
		}
	}

	/**
	 * Adds a processor to the group
	 * @param p The processor to add
	 * @return A reference to the current group processor
	 */
	public GroupProcessor addProcessor(Processor p)
	{
		m_processors.add(p);
		return this;
	}

	/**
	 * Adds multiple processors to the group
	 * @param procs The processors to add
	 * @return A reference to the current group processor
	 */
	public GroupProcessor addProcessors(Processor... procs)
	{
		for (Processor p : procs)
		{
			m_processors.add(p);
		}
		return this;
	}
	
	/**
	 * Declares that the <i>i</i>-th input of the group is linked to the
	 * <i>j</i>-th input of processor <code>p</code>
	 * @param i The number of the input of the group
	 * @param p The processor to connect to
	 * @param j The number of the input of processor <code>p</code>
	 * @return A reference to the current group processor
	 */
	public GroupProcessor associateInput(int i, Processor p, int j)
	{
		setPushableInput(i, p.getPushableInput(j));
		setPullableInputAssociation(i, p, j);
		return this;
	}
	
	/**
	 * Declares that the <i>i/</i>-th output of the group is linked to the
	 * <i>j</i>-th output of processor p
	 * @param i The number of the output of the group
	 * @param p The processor to connect to
	 * @param j The number of the output of processor <code>p</code>
	 * @return A reference to the current group processor
	 */
	public GroupProcessor associateOutput(int i, Processor p, int j)
	{
		setPullableOutput(i, p.getPullableOutput(j));
		setPushableOutputAssociation(i, p, j);
		return this;
	}

	@Override
	public final Pushable getPushableInput(int index)
	{
		return m_inputPushables.get(index);
	}

	@Override
	public final Pullable getPullableOutput(int index)
	{
		return m_outputPullables.get(index);
	}
	
	@Override
	public final void setPullableInput(int i, Pullable p)
	{
		ProcessorAssociation a = m_inputPullableAssociations.get(i);
		a.m_processor.setPullableInput(a.m_outputNumber, p);
	}

	public final void setPushableOutputAssociation(int i, Processor p, int j)
	{
		m_outputPushableAssociations.put(i, new GroupProcessor.ProcessorAssociation(j, p));
	}
	
	@Override
	public final void setPushableOutput(int i, Pushable p)
	{
		ProcessorAssociation a = m_outputPushableAssociations.get(i);
		a.m_processor.setPushableOutput(a.m_outputNumber, p);
	}

	public final void setPullableInputAssociation(int i, Processor p, int j)
	{
		m_inputPullableAssociations.put(i, new GroupProcessor.ProcessorAssociation(j, p));
	}

	public final void setPushableInput(int i, Pushable p)
	{
		if (i == m_inputPushables.size())
		{
			m_inputPushables.add(p);
		}
		else
		{
			m_inputPushables.set(i, p);
		}
	}

	public final void setPullableOutput(int i, Pullable p)
	{
		if (i == m_outputPullables.size())
		{
			m_outputPullables.add(p);
		}
		else
		{
			m_outputPullables.set(i, p);	
		}		
	}

	@Override
	public final Pushable getPushableOutput(int index)
	{
		if (index < m_outputPushables.length)
		{
			return m_outputPushables[index];
		}
		return null;
	}
}
