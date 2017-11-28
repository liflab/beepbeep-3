package ca.uqac.lif.cep.sets;

import java.util.Collection;
import java.util.Queue;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.tmf.SinkLast;

public class ProcessOnSet extends SingleProcessor
{
	/**
	 * 
	 */
	private static final long serialVersionUID = 901561737275437783L;

	protected Processor m_processor;

	protected transient SinkLast m_sink;

	protected transient Pushable m_pushable;

	public ProcessOnSet(Processor processor)
	{
		super(1, processor.getOutputArity());
		int out_arity = processor.getOutputArity();
		m_processor = processor;
		m_pushable = m_processor.getPushableInput();
		m_sink = new SinkLast(out_arity);
		Connector.connect(m_processor, m_sink);
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs) throws ProcessorException 
	{
		m_processor.reset();
		if (inputs[0] instanceof Multiset)
		{
			for (Object o : (Multiset) inputs[0])
			{
				m_pushable.push(o);
			}
		}
		else if (inputs[0] instanceof Collection)
		{
			for (Object o : (Collection<?>) inputs[0])
			{
				m_pushable.push(o);
			}
		}
		Object[] last = m_sink.getLast();
		if (last != null)
		{
			Object[] outs = new Object[last.length];
			for (int i = 0; i < last.length; i++)
			{
				outs[i] = last[i];
			}
			outputs.add(outs);
		}
		return true;
	}

	@Override
	public Processor duplicate()
	{
		return new ProcessOnSet(m_processor.duplicate());
	}

}
