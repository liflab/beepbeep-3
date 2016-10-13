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
package ca.uqac.lif.cep;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import ca.uqac.lif.bullwinkle.BnfRule;
import ca.uqac.lif.cep.Connector.ConnectorException;

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
		int m_ioNumber;

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
			m_ioNumber = number;
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
		return new ProxyPushable(m_inputPushables.get(index), index);
		//return m_inputPushables.get(index);
	}

	@Override
	public final Pullable getPullableOutput(int index)
	{
		return new ProxyPullable(m_outputPullables.get(index), index);
		//return m_outputPullables.get(index);
	}

	@Override
	public final void setPullableInput(int i, Pullable p)
	{
		ProcessorAssociation a = m_inputPullableAssociations.get(i);
		a.m_processor.setPullableInput(a.m_ioNumber, p);
	}

	public final void setPushableOutputAssociation(int i, Processor p, int j)
	{
		m_outputPushableAssociations.put(i, new GroupProcessor.ProcessorAssociation(j, p));
	}

	@Override
	public final void setPushableOutput(int i, Pushable p)
	{
		ProcessorAssociation a = m_outputPushableAssociations.get(i);
		a.m_processor.setPushableOutput(a.m_ioNumber, p);
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
		ProcessorAssociation a = m_outputPushableAssociations.get(index);
		return a.m_processor.getPushableOutput(a.m_ioNumber);
	}
	
	@Override
	public final Pullable getPullableInput(int index)
	{
		ProcessorAssociation a = m_inputPullableAssociations.get(index);
		return a.m_processor.getPullableInput(a.m_ioNumber);
	}
	
	public Map<Integer,Processor> cloneInto(GroupProcessor group)
	{
		Map<Integer,Processor> new_procs = new HashMap<Integer,Processor>();
		Processor start = null;
		// Clone every processor of the original group
		for (Processor p : m_processors)
		{
			if (start == null)
			{
				start = p;
			}
			Processor clone_p = p.clone();
			clone_p.setContext(p.m_context);
			new_procs.put(p.getId(), clone_p);
			group.addProcessor(clone_p);
		}
		// Re-pipe the inputs like in the original group
		for (Integer input_number : m_inputPullableAssociations.keySet())
		{
			ProcessorAssociation pa = m_inputPullableAssociations.get(input_number);
			Processor clone_p = new_procs.get(pa.m_processor.getId());
			group.associateInput(input_number, clone_p, pa.m_ioNumber);
		}
		// Re-pipe the outputs like in the original group
		for (Integer output_number : m_outputPushableAssociations.keySet())
		{
			ProcessorAssociation pa = m_outputPushableAssociations.get(output_number);
			Processor clone_p = new_procs.get(pa.m_processor.getId());
			group.associateOutput(output_number, clone_p, pa.m_ioNumber);
		}
		// Re-pipe the internal processors like in the original group
		CopyCrawler cc = new CopyCrawler(new_procs);
		cc.crawl(start);
		return new_procs;
	}

	@Override
	public GroupProcessor clone()
	{
		GroupProcessor group = new GroupProcessor(getInputArity(), getOutputArity());
		cloneInto(group);
		return group;
	}

	/**
	 * Crawler that creates copies (clones) of whatever it encounters
	 * on its way
	 * @author Sylvain Hallé
	 */
	protected static class CopyCrawler extends PipeCrawler
	{
		Map<Integer,Processor> m_correspondences;

		public CopyCrawler(Map<Integer,Processor> correspondences)
		{
			super();
			m_correspondences = correspondences;
		}

		@Override
		public void visit(Processor p)
		{
			int out_arity = p.getOutputArity();
			for (int i = 0; i < out_arity; i++)
			{
				Pushable push = p.getPushableOutput(i);
				if (push != null)
				{
					Processor target = push.getProcessor();
					int j = push.getPosition();
					Processor new_p = m_correspondences.get(p.getId());
					Processor new_target = m_correspondences.get(target.getId());
					if (new_p != null && new_target != null)
					{
						// new_p and new_target may be null if they refer to a processor
						// outside of the group
						try 
						{
							Connector.connect(new_p, new_target, i, j);
						} 
						catch (ConnectorException e) 
						{
							e.printStackTrace();
						}
					}
				}
			}
		}
	}

	@Override
	public void setContext(Context context)
	{
		super.setContext(context);
		for (Processor p : m_processors)
		{
			p.setContext(context);
		}
	}

	@Override
	public void setContext(String key, Object value)
	{
		super.setContext(key, value);
		for (Processor p : m_processors)
		{
			p.setContext(key, value);
		}
	}
	
	public class ProxyPullable implements Pullable
	{
		protected Pullable m_pullable;
		
		public Object pull() {
			return m_pullable.pull();
		}

		public Object pullHard() {
			return m_pullable.pullHard();
		}

		public NextStatus hasNext() {
			return m_pullable.hasNext();
		}

		public NextStatus hasNextHard() {
			return m_pullable.hasNextHard();
		}

		public int getPullCount() {
			return m_pullable.getPullCount();
		}

		public Processor getProcessor() {
			return GroupProcessor.this;
		}

		public int getPosition() {
			return m_position;
		}

		protected int m_position = 0;	
		
		public ProxyPullable(Pullable p, int position)
		{
			super();
			m_pullable = p;
			m_position = position;
		}
	}
	
	public class ProxyPushable implements Pushable
	{
		protected Pushable m_pushable;
		
		protected int m_position = 0;
		
		public ProxyPushable(Pushable p, int position)
		{
			super();
			m_pushable = p;
			m_position = position;
		}

		@Override
		public Pushable push(Object o)
		{
			return m_pushable.push(o);
		}

		@Override
		public int getPushCount() 
		{
			return m_pushable.getPushCount();
		}

		@Override
		public Processor getProcessor() 
		{
			return GroupProcessor.this;
		}

		@Override
		public int getPosition() 
		{
			return m_position;
		}
	}
	
}
