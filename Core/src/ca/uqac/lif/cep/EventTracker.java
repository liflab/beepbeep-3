/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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
import java.util.Map;

import ca.uqac.lif.cep.EventFunction.InputValue;
import ca.uqac.lif.petitpoucet.BrokenChain;
import ca.uqac.lif.petitpoucet.NodeFunction;
import ca.uqac.lif.petitpoucet.ProvenanceNode;

/**
 * Tracks the relationship between output events produced by processors, and
 * the input events that were used to compute them.
 * {@link ca.uqac.lif.cep.Processor Processor} objects can be associated to a
 * tracker. When this is the case, they <em>may</em> call the tracker, asking 
 * it to record a relationship between events. The tracker can use this set
 * of recorded relationships, potentially coming from multiple processors, to
 * reconstruct the chain of computation leading to a particular event.
 * <p>
 * This tracking is done by processors on a "voluntary" basis. If a processor
 * does not call the tracker to record these relationships, the chain of
 * dependencies may be broken at some point.
 * 
 * @author Sylvain Hallé
 */
public class EventTracker 
{
	/**
	 * A map containing all the input-output associations recorded so far.
	 * This map is a three-tiered nested data structure:
	 * <ul>
	 * <li>At the first level, it associates processor IDs to maps</li>
	 * <li>The resulting object is itself a map that associates stream
	 * indices for this processor to a map</li>
	 * <li>The resulting object is a map that associates positions in
	 * that stream to a {@link ca.uqac.lif.petitpoucet.ProvenanceNode ProvenanceNode}</li>  
	 * </ul>
	 * The structure could have been a simple set of {@code ProvenanceNode}s. However,
	 * if we know the processor ID, the stream index and the stream position, finding
	 * the corresponding node requires three hash lookups in the present structure,
	 * instead of a linear search through an unordered set (or list).
	 */
	protected final Map<Integer,Map<Integer,Map<Integer,ProvenanceNode>>> m_mapping = new HashMap<Integer,Map<Integer,Map<Integer,ProvenanceNode>>>();
	
	protected final Map<Integer,Map<Integer,ProcessorConnection>> m_inputConnections = new HashMap<Integer,Map<Integer,ProcessorConnection>>();
	
	protected final Map<Integer,Map<Integer,ProcessorConnection>> m_outputConnections = new HashMap<Integer,Map<Integer,ProcessorConnection>>();
	
	protected void setConnection(Map<Integer,Map<Integer,ProcessorConnection>> map, int source_proc_id, int stream_index, ProcessorConnection connection)
	{
		if (!map.containsKey(source_proc_id))
		{
			map.put(source_proc_id, new HashMap<Integer,ProcessorConnection>());
		}
		Map<Integer,ProcessorConnection> m1 = map.get(source_proc_id);
		m1.put(stream_index, connection);
	}
	
	protected /*@Null*/ ProcessorConnection getConnection(Map<Integer,Map<Integer,ProcessorConnection>> map, int source_proc_id, int stream_index)
	{
		if (!map.containsKey(source_proc_id))
		{
			return null;
		}
		Map<Integer,ProcessorConnection> m1 = map.get(source_proc_id);
		if (!m1.containsKey(stream_index))
		{
			return null;
		}
		return m1.get(stream_index);
	}

	/**
	 * Associates an output event from a processor to an arbitrary node function 
	 * @param id The ID of the processor
	 * @param f The node function
	 * @param out_stream_index The index of the stream in the processor where
	 *  this output event is produced
	 * @param out_stream_pos The position in the stream corresponding to this
	 *  output event
	 */
	public void associateTo(int id, NodeFunction f, int out_stream_index, int out_stream_pos)
	{
		ProvenanceNode pn_child = fetchOrCreateProvenanceNode(id, out_stream_index, out_stream_pos);
		ProvenanceNode pn_parent = new ProvenanceNode(f);
		pn_child.addParent(pn_parent);
	}
	
	/**
	 * Associates an output event from a processor to an input event from
	 * that same processor 
	 * @param id The ID of the processor
	 * @param in_stream_index The index of the stream in the processor
	 *  corresponding to the input event to associate
	 * @param in_stream_pos The position in the input stream corresponding to
	 *  this event
	 * @param out_stream_index The index of the stream in the processor where
	 *  the output event is produced
	 * @param out_stream_pos The position in the stream corresponding to this
	 *  output event
	 */
	public void associateToInput(int id, int in_stream_index, int in_stream_pos, int out_stream_index, int out_stream_pos)
	{
		ProvenanceNode pn_child = fetchOrCreateProvenanceNode(id, out_stream_index, out_stream_pos);
		ProvenanceNode pn_parent = new ProvenanceNode(new EventFunction.InputValue(-1, in_stream_index, in_stream_pos));
		pn_child.addParent(pn_parent);
	}
	
	/**
	 * Associates an output event from a processor to another output event from
	 * that same processor 
	 * @param id The ID of the processor
	 * @param in_stream_index The index of the stream in the processor
	 *  corresponding to the input event to associate
	 * @param in_stream_pos The position in the input stream corresponding to
	 *  this event
	 * @param out_stream_index The index of the stream in the processor where
	 *  the output event is produced
	 * @param out_stream_pos The position in the stream corresponding to this
	 *  output event
	 */
	public void associateToOutput(int id, int in_stream_index, int in_stream_pos, int out_stream_index, int out_stream_pos)
	{
		ProvenanceNode pn_child = fetchOrCreateProvenanceNode(id, out_stream_index, out_stream_pos);
		ProvenanceNode pn_parent = new ProvenanceNode(new EventFunction.OutputValue(id, in_stream_index, in_stream_pos));
		pn_child.addParent(pn_parent);
	}
	
	/**
	 * Associates this tracker to multiple processors at the same time.
	 * @param processors The processors this tracker should be associated
	 * to
	 */
	public void setTo(Processor ... processors)
	{
		for (Processor p : processors)
		{
			p.setEventTracker(this);
		}
	}
	
	/**
	 * Fetches the {@link ca.uqac.lif.petitpoucet.ProvenanceNode ProvenanceNode}
	 * for a given processor/index/position triplet. Since these nodes are stored
	 * in a bunch of nested hash maps, and that the maps for the desired keys may
	 * have not been initialized yet, the method takes care of creating empty
	 * maps as it drills down its way to the node it is looking for. 
	 * @see #m_mapping
	 * @param proc_id The ID of the processor
	 * @param stream_index The index of the output stream on that processor
	 * @param stream_pos The position of the event in that stream
	 * @return The provenance node corresponding to that particular event
	 */
	protected ProvenanceNode fetchOrCreateProvenanceNode(int proc_id, int stream_index, int stream_pos)
	{
		if (!m_mapping.containsKey(proc_id))
		{
			m_mapping.put(proc_id, new HashMap<Integer,Map<Integer,ProvenanceNode>>());
		}
		Map<Integer,Map<Integer,ProvenanceNode>> m1 = m_mapping.get(proc_id);
		if (!m1.containsKey(stream_index))
		{
			m1.put(stream_index, new HashMap<Integer,ProvenanceNode>());
		}
		Map<Integer,ProvenanceNode> m2 = m1.get(stream_index);
		if (!m2.containsKey(stream_pos))
		{
			m2.put(stream_pos, new ProvenanceNode(new EventFunction.OutputValue(proc_id, stream_index, stream_pos)));
		}
		return (ProvenanceNode) m2.get(stream_pos);
	}
	
	/**
	 * Fetches the {@link ca.uqac.lif.petitpoucet.ProvenanceNode ProvenanceNode}
	 * for a given processor/index/position triplet. Contrast this to
	 * {@link #fetchOrCreateProvenanceNode(int, int, int) fetchOrCreateProvenanceNode()}. 
	 * @param proc_id The ID of the processor
	 * @param stream_index The index of the output stream on that processor
	 * @param stream_pos The position of the event in that stream
	 * @return The provenance node corresponding to that particular event, or
	 *   {@code null} if no node exists for the specified parameters
	 */
	protected ProvenanceNode fetchProvenanceNode(int proc_id, int stream_index, int stream_pos)
	{
		if (!m_mapping.containsKey(proc_id))
		{
			return null;
		}
		Map<Integer,Map<Integer,ProvenanceNode>> m1 = m_mapping.get(proc_id);
		if (!m1.containsKey(stream_index))
		{
			return null;
		}
		Map<Integer,ProvenanceNode> m2 = m1.get(stream_index);
		if (!m2.containsKey(stream_pos))
		{
			return null;
		}
		return (ProvenanceNode) m2.get(stream_pos);
	}
	
	/**
	 * Gets the provenance tree for a given event.
	 * @param proc_id
	 * @param stream_index
	 * @param stream_pos
	 * @return
	 */
	public /*@NotNull*/ ProvenanceNode getProvenanceTree(int proc_id, int stream_index, int stream_pos)
	{
		ProvenanceNode node = fetchProvenanceNode(proc_id, stream_index, stream_pos);
		if (node == null)
		{
			return BrokenChain.instance;
		}
		ProvenanceNode expanded_node = new ProvenanceNode(node.getNodeFunction());
		for (ProvenanceNode parent : node.getParents())
		{
			ProvenanceNode new_parent;
			NodeFunction nf = parent.getNodeFunction();
			if (nf instanceof InputValue)
			{
				InputValue iv = (InputValue) nf;
				// Try to find what processor produced the event
				// that was given as an input to this processor
				ProcessorConnection pc = getConnection(m_inputConnections, proc_id, iv.m_streamIndex);
				if (pc == null)
				{
					// Not found; declare a broken chain
					new_parent = BrokenChain.instance;
				}
				else
				{
					// Found it: recurse
					new_parent = getProvenanceTree(pc.m_procId, pc.m_streamIndex, iv.m_streamPosition);
				}
			}
			else
			{
				new_parent = parent;
			}
			expanded_node.addParent(new_parent);
		}
		return expanded_node;
	}
	
	public void setConnection(int output_proc_id, int output_stream_index, int input_proc_id, int input_stream_index)
	{
		setConnection(m_inputConnections, input_proc_id, input_stream_index, new ProcessorConnection(output_proc_id, output_stream_index));
		setConnection(m_outputConnections, output_proc_id, output_stream_index, new ProcessorConnection(input_proc_id, input_stream_index));
	}
	
	protected static class ProcessorConnection
	{
		public int m_procId;
		public int m_streamIndex;
		
		public ProcessorConnection(int proc_id, int stream_index)
		{
			super();
			m_procId = proc_id;
			m_streamIndex = stream_index;
		}
		
		@Override
		public String toString()
		{
			return "P" + m_procId + "." + m_streamIndex; 
		}
	}
}
