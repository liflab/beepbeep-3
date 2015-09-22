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
package ca.uqac.lif.cep;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.Vector;

import ca.uqac.lif.bullwinkle.BnfRule;

public class GroupProcessor extends Processor
{
	protected Set<Processor> m_processors = null;

	protected Vector<Pushable> m_inputPushables = null;

	protected Vector<Pullable> m_outputPullables = null;
	
	protected Map<Integer,ProcessorAssociation> m_inputPullableAssociations;
	
	protected Map<Integer,ProcessorAssociation> m_outputPushableAssociations;
	
	protected String m_ruleName;
	
	protected BnfRule m_rule;

	public GroupProcessor(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
		m_processors = new HashSet<Processor>();
		m_inputPushables = new Vector<Pushable>();
		m_outputPullables = new Vector<Pullable>();
		m_inputPullableAssociations = new HashMap<Integer,ProcessorAssociation>();
		m_outputPushableAssociations = new HashMap<Integer,ProcessorAssociation>();
	}
	
	public void setRuleName(String rule_name)
	{
		m_ruleName = rule_name;
	}
	
	public String getRuleName()
	{
		return m_ruleName;
	}
	
	public BnfRule getRule()
	{
		return m_rule;
	}
	
	protected static class ProcessorAssociation
	{
		int m_outputNumber;
		Processor m_processor;
		
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
	 */
	public void addProcessor(Processor p)
	{
		m_processors.add(p);
	}
	
	/**
	 * Declares that the <i>i</i>-th input of the group is linked to the
	 * <i>j</i>-th input of processor <code>p</code>
	 * @param i The number of the input of the group
	 * @param p The processor to connect to
	 * @param j The number of the input of processor <code>p</code>
	 */
	public void associateInput(int i, Processor p, int j)
	{
		setPushableInput(i, p.getPushableInput(j));
		setPullableInputAssociation(i, p, j);
	}
	
	/**
	 * Declares that the <i>i/</i>-th output of the group is linked to the
	 * <i>j</i>-th output of processor p
	 * @param i The number of the output of the group
	 * @param p The processor to connect to
	 * @param j The number of the output of processor <code>p</code>
	 */
	public void associateOutput(int i, Processor p, int j)
	{
		setPullableOutput(i, p.getPullableOutput(j));
		setPushableOutputAssociation(i, p, j);
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
		return m_outputPushables.get(index);
	}
	
	@Override
	public void build(Stack<Object> stack)
	{
		// TODO
	}
	
	@Override
	public GroupProcessor newInstance()
	{
		return new GroupProcessor(getInputArity(), getOutputArity());
	}



}
