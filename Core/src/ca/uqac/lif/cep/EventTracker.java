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
public interface EventTracker
{
	/**
	 * Associates an output event from a processor to an arbitrary node function 
	 * @param id The ID of the processor
	 * @param f The node function
	 * @param out_stream_index The index of the stream in the processor where
	 *  this output event is produced
	 * @param out_stream_pos The position in the stream corresponding to this
	 *  output event
	 */
	public void associateTo(int id, NodeFunction f, int out_stream_index, int out_stream_pos);
	
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
	public void associateToInput(int id, int in_stream_index, int in_stream_pos, int out_stream_index, int out_stream_pos);
	
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
	public void associateToOutput(int id, int in_stream_index, int in_stream_pos, int out_stream_index, int out_stream_pos);
	
	/**
	 * Gets the provenance tree for a given event.
	 * @param proc_id The ID of the prcoessor
	 * @param stream_index The index of the stream in the processor
	 *  corresponding to the input event to associate
	 * @param stream_pos  The position in the stream corresponding to
	 *  this event
	 * @return The provenance tree
	 */
	public /*@NotNull*/ ProvenanceNode getProvenanceTree(int proc_id, int stream_index, int stream_pos);
	
	public void setConnection(int output_proc_id, int output_stream_index, int input_proc_id, int input_stream_index);
	
	/**
	 * Associates this tracker to multiple processors at the same time.
	 * @param processors The processors this tracker should be associated
	 * to
	 */
	public void setTo(Processor ... processors);
	
	/**
	 * A single instance of a "no-op" event tracker
	 */
	public NoOpEventTracker NOOP_TRACKER = new NoOpEventTracker();
	
	/**
	 * Dummy event tracker that does nothing
	 */
	public class NoOpEventTracker implements EventTracker
	{
		private NoOpEventTracker()
		{
			super();
		}
		
		@Override
		public void associateTo(int id, NodeFunction f, int out_stream_index, int out_stream_pos) 
		{
			// Do nothing
		}

		@Override
		public void associateToInput(int id, int in_stream_index, int in_stream_pos, int out_stream_index, int out_stream_pos) 
		{
			// Do nothing
		}

		@Override
		public void associateToOutput(int id, int in_stream_index, int in_stream_pos, int out_stream_index, int out_stream_pos) 
		{
			// Do nothing
		}

		@Override
		public ProvenanceNode getProvenanceTree(int proc_id, int stream_index, int stream_pos) 
		{
			return BrokenChain.instance;	
		}

		@Override
		public void setConnection(int output_proc_id, int output_stream_index, int input_proc_id, int input_stream_index) 
		{
			// Do nothing	
		}

		@Override
		public void setTo(Processor... processors)
		{
			// Do nothing
		}
	}
}