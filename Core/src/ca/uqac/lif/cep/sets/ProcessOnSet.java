package ca.uqac.lif.cep.sets;

import java.util.Collection;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.UniformProcessor;
import ca.uqac.lif.cep.tmf.SinkLast;

public class ProcessOnSet extends UniformProcessor
{
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
		try
		{
			Connector.connect(m_processor, m_sink);
		} 
		catch (ConnectorException e) 
		{
			// Not much to do
			e.printStackTrace();
		}
	}

	@Override
	protected boolean compute(Object[] inputs, Object[] outputs) throws ProcessorException 
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
		for (int i = 0; i < outputs.length; i++)
		{
			outputs[i] = last[i];
		}
		return true;
	}

	@Override
	public Processor clone()
	{
		return new ProcessOnSet(m_processor.clone());
	}

}
