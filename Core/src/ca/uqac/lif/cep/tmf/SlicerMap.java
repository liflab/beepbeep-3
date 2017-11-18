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
package ca.uqac.lif.cep.tmf;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.UniformProcessor;
import ca.uqac.lif.cep.functions.Function;
import ca.uqac.lif.cep.functions.FunctionException;
import ca.uqac.lif.cep.util.BeepBeepLogger;

/**
 * Separates an input trace into different "slices". The slicer
 * takes as input a processor <i>p</i> and
 * a slicing function <i>f</i>.
 * There exists potentially one instance of <i>p</i> for each value
 * in the image of <i>f</i>.
 * <p>
 * When an event <i>e</i> arrives, the slicer evaluates
 * <i>c</i> = <i>f</i>(<i>e</i>). This value determines to what instance
 * of <i>p</i> the event will be dispatched.
 * <p>
 * The function <i>f</i> may return <code>null</code>, or the special
 * object {@link AllSlices}. This indicates that no new slice must
 * be created, but that the incoming event must be dispatched to
 * <em>all</em> slices one by one. In such a case, the output of
 * every slice on that event is sent out, in no particular order.
 * 
 * @author Sylvain Hallé
 */
public class SlicerMap extends UniformProcessor
{
	/**
	 * The slicing function
	 */
	protected Function m_slicingFunction = null;

	/**
	 * The internal processor
	 */
	protected Processor m_processor = null;

	protected Map<Object,Processor> m_slices;

	protected Map<Object,QueueSink> m_sinks;
	
	/**
	 * The last values output by every slice 
	 */
	protected Map<Object,Object> m_values;

	SlicerMap()
	{
		super(1, 1);
	}

	public SlicerMap(/*@NonNull*/ Function func, /*@NonNull*/ Processor proc)
	{
		super(proc.getInputArity(), proc.getOutputArity());
		m_processor = proc;
		m_slicingFunction = func;
		m_slices = new HashMap<Object,Processor>();
		m_sinks = new HashMap<Object,QueueSink>();
		m_values = new HashMap<Object,Object>();
	}

	@Override
	protected boolean compute(Object[] inputs, Object[] outputs) throws ProcessorException
	{
		int output_arity = getOutputArity();
		Object[] f_value = new Object[1];
		try
		{
			m_slicingFunction.evaluate(inputs, f_value);
		}
		catch (FunctionException e)
		{
			throw new ProcessorException(e);
		}
		Object slice_id = f_value[0];
		Set<Object> slices_to_process = new HashSet<Object>();
		if (slice_id instanceof AllSlices || slice_id == null)
		{
			slices_to_process.addAll(m_slices.keySet());
		}
		else
		{
			if (!m_slices.containsKey(slice_id))
			{
				// First time we see this value: create new slice
				Processor p = m_processor.clone();
				m_slices.put(slice_id, p);
				addContextFromSlice(p, slice_id);
				QueueSink sink = new QueueSink(output_arity);
				try
				{
					Connector.connect(p, sink);
				}
				catch (ConnectorException e)
				{
					BeepBeepLogger.logger.log(Level.SEVERE, "", e);
				}
				m_sinks.put(slice_id, sink);
			}
			slices_to_process.add(slice_id);
		}
		for (Object s_id : slices_to_process)
		{
			// Find processor corresponding to that slice
			Processor slice_p = m_slices.get(s_id);
			QueueSink sink_p = m_sinks.get(s_id);
			// Push the input into the processor
			Pushable[] p_array = new Pushable[inputs.length];
			for (int i = 0; i < inputs.length; i++)
			{

				Object o_i = inputs[i];
				Pushable p = slice_p.getPushableInput(i);
				p.push(o_i);
				p_array[i] = p;
			}
			for (int i = 0; i < inputs.length; i++)
			{
				p_array[i].waitFor();
			}
			// Collect the output from that processor
			if (!sink_p.getQueue().isEmpty())
			{
				m_values.put(s_id, sink_p.remove()[0]);
			}
		}
		outputs[0] = m_values;
		return true;
	}

	public void addContextFromSlice(Processor p, Object slice)
	{
		// Do nothing
	}

	@Override
	public void reset()
	{
		super.reset();
		m_slices.clear();
		m_slicingFunction.reset();
	}

	public static void build(ArrayDeque<Object> stack) throws ConnectorException
	{
		Function f = (Function) stack.pop();
		stack.pop(); // ON
		//stack.pop(); // (
		Processor p2 = (Processor) stack.pop();
		//stack.pop(); // )
		stack.pop(); // WITH
		//stack.pop(); // (
		Processor p1 = (Processor) stack.pop();
		//stack.pop(); // )
		stack.pop(); // SLICE
		SlicerMap out = new SlicerMap(f, p2);
		Connector.connect(p1, out);
		stack.push(out);
	}

	@Override
	public SlicerMap clone()
	{
		return new SlicerMap(m_slicingFunction.clone(m_context), m_processor.clone());
	}

	/**
	 * Dummy object telling the slicer that the event must be sent to
	 * all slices
	 */
	public static class AllSlices
	{
		public static final transient AllSlices instance = new AllSlices();

		AllSlices()
		{
			super();
		}
	}
}
