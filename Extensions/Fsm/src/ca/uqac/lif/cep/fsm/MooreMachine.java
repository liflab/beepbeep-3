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
package ca.uqac.lif.cep.fsm;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.SingleProcessor;

/**
 * A finite-state automaton with output symbols associated to its states.
 * Its input arity is not fixed to 1, i.e. it can read events from
 * multiple traces at once. (Although, theoretically, this can be reduced
 * to the unary case, so this is not a genuine generalization.)
 * <p>
 * A "classical" finite-state automaton is a particular case of Moore
 * machine where one simply ignores any output symbols. In that context,
 * accepting and rejecting states can simply be associated to two
 * different, arbitrary symbols (e.g. <code>true</code> and 
 * <code>false</code>).
 *  
 * @author Sylvain Hallé
 *
 */
public class MooreMachine extends SingleProcessor
{
	/**
	 * A map from a state to the list of transitions from that
	 * state
	 */
	protected Map<Integer,List<Transition>> m_relation;
	
	/**
	 * Associates output symbols to the states of the machine
	 */
	protected Map<Integer,Object[]> m_outputSymbols;
	
	/**
	 * The current state the machine is in
	 */
	protected int m_currentState;
	
	/**
	 * The initial state of the machine
	 */
	protected int m_initialState;
	
	public MooreMachine(int in_arity, int out_arity)
	{
		super(in_arity, out_arity);
		m_relation = new HashMap<Integer,List<Transition>>();
		m_outputSymbols = new HashMap<Integer,Object[]>();
		m_currentState = 0;
		m_initialState = 0;
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_currentState = m_initialState;
		// Reset transitions
		for (int source : m_relation.keySet())
		{
			List<Transition> trans = m_relation.get(source);
			for (Transition t : trans)
			{
				t.reset();
			}
		}
	}
	
	/**
	 * Associates output symbols (i.e. event) to a state of the
	 * Moore machine
	 * @param state The state
	 * @param symbols The symbols to associate. This will be the output
	 *   event produced whenever the machine takes a transition ending in
	 *   that state. There should be as many symbols as the output arity
	 *   of the machine
	 * @return A reference to the current Moore machine
	 */
	public MooreMachine addSymbols(int state, Object[] symbols)
	{
		m_outputSymbols.put(state, symbols);
		return this;
	}
	
	/**
	 * Associates an output symbol (i.e. event) to a state of the
	 * Moore machine
	 * @param state The state
	 * @param symbol The symbol to associate. This will be the output
	 *   event produced whenever the machine takes a transition ending in
	 *   that state. There should be as many symbols as the output arity
	 *   of the machine. Therefore this method should only be called on a
	 *   Moore machine of output arity 1.
	 * @return A reference to the current Moore machine
	 */
	public MooreMachine addSymbol(int state, Object symbol)
	{
		Object[] symbols = new Object[1];
		symbols[0] = symbol;
		return addSymbols(state, symbols);
	}
	
	/**
	 * Adds a transition to the machine
	 * @param source The source state
	 * @param t The transition to add
	 * @return A reference to the current Moore machine
	 */
	public MooreMachine addTransition(int source, Transition t)
	{
		if (!m_relation.containsKey(source))
		{
			m_relation.put(source, new ArrayList<Transition>());
		}
		List<Transition> list = m_relation.get(source);
		list.add(t);
		return this;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		List<Transition> transitions = m_relation.get(m_currentState);
		//System.out.println(inputs[0]);
		Transition otherwise = null;
		for (Transition t : transitions)
		{
			if (t instanceof TransitionOtherwise)
			{
				otherwise = t;
			}
			else
			{
				if (t.isFired(inputs, m_context))
				{
					// This transition fires: move to that state
					return fire(t, inputs);
				}
			}
		}
		if (otherwise != null)
		{
			// No "normal" transition has fired, but we have an "otherwise": fire it
			return fire(otherwise, inputs);
		}
		// Screwed: no transition defined for this input
		return null;
	}
	
	/**
	 * Fires a transition and updates the machine's state
	 * @param t The transition to fire
	 * @param inputs The inputs that caused the transition to fire
	 * @return Any output symbol associated with the destination state,
	 *   <code>null</code> otherwise
	 */
	protected Queue<Object[]> fire(Transition t, Object[] inputs)
	{
		m_currentState = t.getDestination();
		t.modifyContext(inputs, this);
		//System.out.println(t);
		//System.out.println(m_context);
		// Anything to output?
		if (m_outputSymbols.containsKey(m_currentState))
		{
			return wrapVector(m_outputSymbols.get(m_currentState));
		}
		return null;
	}

	/**
	 * Represents a transition in the Moore machine
	 * @author Sylvain Hallé
	 *
	 */
	public static class Transition
	{
		/**
		 * Creates a new transition
		 */
		public Transition()
		{
			super();
		}
		
		/**
		 * Copies a transition from another transition
		 * @param t The transition to copy from
		 */
		public Transition(Transition t)
		{
			super();
		}
		
		/**
		 * Determines if the transition fires for the given input
		 * @param inputs The input events
		 * @param context The context for the evaluation
		 * @return <code>true</code> if the transition fires, <code>false</code>
		 *   otherwise
		 */
		public boolean isFired(Object[] inputs, Context context)
		{
			return false;
		}
		
		/**
		 * Resets the state of the transition
		 */
		public void reset()
		{
			// Do nothing
		}
		
		/**
		 * Modifies the context of the state machine
		 */
		public void modifyContext(Object[] inputs, MooreMachine machine)
		{
			// Do nothing
		}
		
		/**
		 * Gets the destination (i.e. target state) of that transition
		 * @return The destination state 
		 */
		public int getDestination()
		{
			return 0;
		}
		
		@Override
		public Transition clone()
		{
			Transition out = new Transition(this);
			return out;
		}
	}
	
	/**
	 * Represents the "otherwise" transition in the Moore machine
	 * @author Sylvain Hallé
	 *
	 */
	public static final class TransitionOtherwise extends Transition
	{
		/**
		 * The destination state of that transition
		 */
		private final int m_destination;
		
		public TransitionOtherwise(TransitionOtherwise t)
		{
			super();
			m_destination = t.m_destination;
		}
		
		public TransitionOtherwise(int destination)
		{
			super();
			m_destination = destination;
		}
		
		@Override
		public boolean isFired(Object[] inputs, Context context)
		{
			return true;
		}
		
		@Override
		public int getDestination()
		{
			return m_destination;
		}
		
		@Override
		public TransitionOtherwise clone()
		{
			return new TransitionOtherwise(this);
		}
		
		@Override
		public String toString()
		{
			return "* -> " + m_destination;
		}
	}
	
	@Override
	public MooreMachine clone()
	{
		MooreMachine out = new MooreMachine(getInputArity(), getOutputArity());
		out.m_initialState = m_initialState;
		out.m_outputSymbols = m_outputSymbols;
		out.m_relation = new HashMap<Integer,List<Transition>>();
		for (int k : m_relation.keySet())
		{
			List<Transition> lt = m_relation.get(k);
			List<Transition> new_lt = new ArrayList<Transition>();
			for (Transition t : lt)
			{
				new_lt.add(t.clone());
			}
			out.m_relation.put(k, new_lt);
		}
		return out;
	}
	
}
