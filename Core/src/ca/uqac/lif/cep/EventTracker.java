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

import ca.uqac.lif.petitpoucet.NodeFunction;
import ca.uqac.lif.petitpoucet.ProvenanceNode;

public class EventTracker 
{
	protected final Map<Integer,Map<Integer,Map<Integer,ProvenanceNode>>> m_mapping = new HashMap<Integer,Map<Integer,Map<Integer,ProvenanceNode>>>();
	
	public void associateTo(int id, NodeFunction f, int out_stream_index, int out_stream_pos)
	{
		ProvenanceNode pn_child = getProvenanceNode(id, out_stream_index, out_stream_pos);
		ProvenanceNode pn_parent = new ProvenanceNode(f);
		pn_child.addParent(pn_parent);
	}
	
	public void associateToInput(int id, int in_stream_index, int in_stream_pos, int out_stream_index, int out_stream_pos)
	{
		ProvenanceNode pn_child = getProvenanceNode(id, out_stream_index, out_stream_pos);
		ProvenanceNode pn_parent = new ProvenanceNode(new InputValue(-1, in_stream_index, in_stream_pos));
		pn_child.addParent(pn_parent);
	}
	
	public void associateToOutput(int id, int in_stream_index, int in_stream_pos, int out_stream_index, int out_stream_pos)
	{
		ProvenanceNode pn_child = getProvenanceNode(id, out_stream_index, out_stream_pos);
		ProvenanceNode pn_parent = new ProvenanceNode(new OutputValue(id, in_stream_index, in_stream_pos));
		pn_child.addParent(pn_parent);
	}
	
	public void setTo(Processor ... processors)
	{
		for (Processor p : processors)
		{
			p.setEventTracker(this);
		}
	}
	
	public ProvenanceNode getProvenanceNode(int proc_id, int stream_index, int stream_pos)
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
			
			m2.put(stream_pos, new ProvenanceNode(new OutputValue(proc_id, stream_index, stream_pos)));
		}
		return (ProvenanceNode) m2.get(stream_pos);
	}
	
	protected static class IndexPos
	{
		public int index;
		public int pos;
		
		public IndexPos(int i, int p)
		{
			index = i;
			pos = p;
		}
		
		@Override
		public int hashCode()
		{
			return (index + 1) * (pos + 1);
		}
		
		@Override
		public boolean equals(Object o)
		{
			if (o == null || !(o instanceof IndexPos))
				return false;
			IndexPos ip = (IndexPos) o;
			return ip.index == index && ip.pos == pos;
		}
	}
}
