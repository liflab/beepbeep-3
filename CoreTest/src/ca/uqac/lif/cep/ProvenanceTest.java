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

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.tmf.Passthrough;
import ca.uqac.lif.cep.tmf.QueueSource;
import ca.uqac.lif.petitpoucet.BrokenChain;
import ca.uqac.lif.petitpoucet.NodeFunction;
import ca.uqac.lif.petitpoucet.ProvenanceNode;

/**
 * Unit tests for provenance features.
 */
public class ProvenanceTest 
{
	@Test
	public void testNoOp1()
	{
		QueueSource source = new QueueSource();
		source.setEvents(new Object[]{1, 2, 3, 4, 5});
		EventTracker tracker = EventTracker.NOOP_TRACKER;
		source.setEventTracker(tracker);
		Pullable p = source.getPullableOutput();
		p.pull();
		ProvenanceNode tree = tracker.getProvenanceTree(source.getId(), 0, 0);
		assertTrue(tree instanceof BrokenChain);
		assertEquals(tracker, source.getEventTracker());
	}
	
	@Test
	public void testNoOp2() throws ConnectorException
	{
		QueueSource source = new QueueSource();
		source.setEvents(new Object[]{1, 2, 3, 4, 5});
		Passthrough pt = new Passthrough();
		Connector.connect(source, pt);
		EventTracker tracker = new DummyTracker();
		tracker.setTo(source, pt);
		Pullable p = pt.getPullableOutput();
		p.pull();
		ProvenanceNode tree = tracker.getProvenanceTree(pt.getId(), 0, 0);
		assertNull(tree);
		assertEquals(tracker, source.getEventTracker());
		assertEquals(tracker, pt.getEventTracker());
	}
	
	/**
	 * A "dummy" event tracker that just records whatever calls have been made
	 * to it. It is used for testing.
	 */
	public static class DummyTracker implements EventTracker
	{
		List<Association> m_inAssociations = new ArrayList<Association>();
		List<Association> m_outAssociations = new ArrayList<Association>();
		List<Association> m_connections = new ArrayList<Association>();
		
		public boolean containsConnection(int out_id, int out_stream_index, int in_id, int in_stream_index)
		{
			for (Association a : m_connections)
			{
				// The attribute names don't match
				if (a.id == out_id && a.in_index == out_stream_index && a.in_pos == in_id &&
						a.out_index == in_stream_index)
					return true;
			}
			return false;
		}
		
		public boolean containsInputAssociation(int id, int in_stream_index,
				int in_stream_pos, int out_stream_index, int out_stream_pos)
		{
			for (Association a : m_inAssociations)
			{
				if (a.id == id && a.in_index == in_stream_index && a.in_pos == in_stream_pos &&
						a.out_index == out_stream_index && a.out_pos == out_stream_pos)
					return true;
			}
			return false;
		}
		
		public boolean containsOutputAssociation(int id, int in_stream_index,
				int in_stream_pos, int out_stream_index, int out_stream_pos)
		{
			for (Association a : m_outAssociations)
			{
				if (a.id == id && a.in_index == in_stream_index && a.in_pos == in_stream_pos &&
						a.out_index == out_stream_index && a.out_pos == out_stream_pos)
					return true;
			}
			return false;
		}

		@Override
		public void associateTo(int id, NodeFunction f, int out_stream_index,
				int out_stream_pos) {
			// TODO Auto-generated method stub
			
		}

		@Override
		public void associateToInput(int id, int in_stream_index,
				int in_stream_pos, int out_stream_index, int out_stream_pos) {
			m_inAssociations.add(new Association(id, in_stream_index, in_stream_pos, out_stream_index, out_stream_pos));
			
		}

		@Override
		public void associateToOutput(int id, int in_stream_index,
				int in_stream_pos, int out_stream_index, int out_stream_pos) {
			m_outAssociations.add(new Association(id, in_stream_index, in_stream_pos, out_stream_index, out_stream_pos));			
		}

		@Override
		public ProvenanceNode getProvenanceTree(int proc_id, int stream_index,
				int stream_pos) {
			// We don't implement this
			return null;
		}

		@Override
		public void setConnection(int output_proc_id, int output_stream_index,
				int input_proc_id, int input_stream_index) {
			m_connections.add(new Association(output_proc_id, output_stream_index, input_proc_id, input_stream_index, -1));
			
		}

		@Override
		public void setTo(Processor... processors)
		{
			for (Processor p : processors)
			{
				p.setEventTracker(this);
			}
		}
		
		public static class Association
		{
			int id;
			int in_index;
			int in_pos;
			int out_index;
			int out_pos;
			
			public Association(int id, int in_index, int in_pos, int out_index, int out_pos)
			{
				this.id = id;
				this.in_index = in_index;
				this.in_pos = in_pos;
				this.out_index = out_index;
				this.out_pos = out_pos;
			}
		}
	}
}
