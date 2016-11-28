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
package ca.uqac.lif.cep.concurrency;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.concurrency.ThroughputMeter.PullMeter;
import ca.uqac.lif.cep.concurrency.ThroughputMeter.PushMeter;

public class ProcessorMeter extends Processor 
{
	protected Processor m_processor;
	
	protected int m_originalId;
	
	protected ThroughputMeter m_meter;
	
	protected String m_description = "";
	
	protected Pullable[] m_inputPullables;
	
	public ProcessorMeter(Processor p, String description, ThroughputMeter meter)
	{
		super(p.getInputArity(), p.getOutputArity());
		m_inputPullables = new Pullable[p.getInputArity()];
		m_outputPushables = new Pushable[p.getOutputArity()];
		m_processor = p;
		m_originalId = m_processor.getId();
		m_description = description;
		m_meter = meter;
	}
	
	protected ProcessorMeter(Processor p, ThroughputMeter meter, int original_id)
	{
		super(p.getInputArity(), p.getOutputArity());
		m_processor = p;
		m_meter = meter;
		m_originalId = original_id;
	}

	@Override
	public Pushable getPushableInput(int index)
	{
		PushMeter pm = m_meter.newInputPushMeter(m_processor, index, m_originalId, m_description);
		return pm;
	}
	
	@Override
	public void setPullableInput(int index, Pullable p)
	{
		//m_inputPullables[index] = p;
		m_processor.setPullableInput(index, p);
	}
	
	@Override
	public void setPushableOutput(int index, Pushable p)
	{
		m_processor.setPushableOutput(index, p);
	}

	@Override
	public Pullable getPullableOutput(int index) 
	{
		PullMeter pm = m_meter.newOutputPullMeter(m_processor, index, m_originalId, m_description);
		return pm;
	}
	
	@Override
	public void setContext(Context c)
	{
		m_processor.setContext(c);
		if (c == null)
		{
			return;
		}
		if (m_context == null)
		{
			m_context = new Context();
		}
		m_context.putAll(c);
	}
	
	@Override
	public void setContext(String key, Object value)
	{
		m_processor.setContext(key, value);
		if (m_context == null)
		{
			m_context = new Context();
		}
		m_context.put(key, value);
	}

	@Override
	public ProcessorMeter clone()
	{
		Processor p_clone = m_processor.clone();
		p_clone.setContext(m_context);
		return new ProcessorMeter(p_clone, m_meter, m_originalId);
	}
}
