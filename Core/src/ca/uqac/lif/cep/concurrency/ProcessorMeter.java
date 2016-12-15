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

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorWrapper;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.concurrency.ThroughputMeter.PullableMeter;
import ca.uqac.lif.cep.concurrency.ThroughputMeter.PushableMeter;

public class ProcessorMeter extends ProcessorWrapper
{
	protected int m_originalId;

	protected ThroughputMeter m_meter;

	protected String m_description = "";

	public ProcessorMeter(Processor p, String description, ThroughputMeter meter)
	{
		super(p);
		m_originalId = m_processor.getId();
		m_description = description;
		m_meter = meter;
		m_meter.registerProcessor(p, description);
	}

	protected ProcessorMeter(Processor p, ThroughputMeter meter, int original_id)
	{
		super(p);
		m_meter = meter;
		m_originalId = original_id;
	}

	@Override
	public Pushable getPushableInput(int index)
	{
		PushableMeter pm = m_meter.newInputPushMeter(m_processor, index, this, m_originalId, m_description);
		return pm;
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		PullableMeter pm = m_meter.newOutputPullMeter(m_processor, index, this, m_originalId, m_description);
		return pm;
	}

	@Override
	public ProcessorMeter clone()
	{
		ProcessorMeter pm = new ProcessorMeter(m_processor.clone(), m_meter, m_originalId);
		super.cloneInto(pm);
		pm.m_description = m_description;
		return pm;
	}
}
