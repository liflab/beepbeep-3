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

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.PullableWrapper;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.PushableWrapper;

public class ThroughputMeter
{
	Map<Integer,Map<Integer,Long>> m_outputPullCount;

	Map<Integer,Map<Integer,Long>> m_outputTotalTime;

	Map<Integer,Map<Integer,Long>> m_inputPushCount;

	Map<Integer,Map<Integer,Long>> m_inputTotalTime;

	Map<Integer,String> m_descriptions;

	public ThroughputMeter()
	{
		super();
		m_outputPullCount = new HashMap<Integer,Map<Integer,Long>>();
		m_inputPushCount = new HashMap<Integer,Map<Integer,Long>>();
		m_outputTotalTime = new HashMap<Integer,Map<Integer,Long>>();
		m_inputTotalTime = new HashMap<Integer,Map<Integer,Long>>();
		m_descriptions = new HashMap<Integer,String>();
	}

	@Override
	public String toString()
	{
		StringBuilder out = new StringBuilder();
		out.append("Mode ID    Description       #        Avg time (ms)\n");
		Set<Integer> processor_ids = m_descriptions.keySet();
		for (int id : processor_ids)
		{
			long cnt = 0;
			long tot_time = 0;
			float avg = 0;
			{
				// Push
				Map<Integer,Long> counts = m_inputPushCount.get(id);
				Map<Integer,Long> times = m_inputTotalTime.get(id);
				for (long c : counts.values())
				{
					cnt += c;
				}
				for (long t : times.values())
				{
					tot_time += t;
				}

				if (cnt > 0)
				{
					avg = ((float) tot_time / (float) cnt) / 1000000f;
				}
				out.append("Push ");
				out.append(pad(Integer.toString(id), 6));
				out.append(pad(m_descriptions.get(id), 18));
				out.append(pad(Long.toString(cnt), 9));
				out.append(avg).append("\n");
			}
			{
				// Pull
				Map<Integer,Long> counts = m_outputPullCount.get(id);
				Map<Integer,Long> times = m_outputTotalTime.get(id);
				for (long c : counts.values())
				{
					cnt += c;
				}
				for (long t : times.values())
				{
					tot_time += t;
				}

				if (cnt > 0)
				{
					avg = ((float) tot_time / (float) cnt) / 1000000f;
				}
				out.append("Pull ");
				out.append(pad(Integer.toString(id), 6));
				out.append(pad(m_descriptions.get(id), 18));
				out.append(pad(Long.toString(cnt), 9));
				out.append(avg).append("\n");
			}
		}
		return out.toString();
	}

	protected static String pad(String s, int width)
	{
		if (s.length() < width)
		{
			for (int i = s.length(); i < width; i++)
			{
				s += " ";
			}
		}
		return s;
	}

	public void registerProcessor(Processor p, String description)
	{
		int id = p.getId();
		m_descriptions.put(id, description);
		{
			Map<Integer,Long> val1 = new HashMap<Integer,Long>();
			Map<Integer,Long> val2 = new HashMap<Integer,Long>();
			for (int i = 0; i < p.getInputArity(); i++)
			{
				val1.put(i, 0l);
				val2.put(i, 0l);
			}
			m_inputPushCount.put(id, val1);
			m_inputTotalTime.put(id, val2);
		}
		{
			Map<Integer,Long> val1 = new HashMap<Integer,Long>();
			Map<Integer,Long> val2 = new HashMap<Integer,Long>();
			for (int i = 0; i < p.getOutputArity(); i++)
			{
				val1.put(i, 0l);
				val2.put(i, 0l);
			}
			m_outputPullCount.put(id, val1);
			m_outputTotalTime.put(id, val2);
		}
	}


	public PushableMeter newInputPushMeter(Processor p, int index, ProcessorMeter pm, int original_id, String description)
	{
		PushableMeter p_meter = new PushableMeter(p.getPushableInput(index), pm, original_id, index);
		return p_meter;
	}

	public PullableMeter newOutputPullMeter(Processor p, int index, Processor reference, int original_id, String description)
	{
		PullableMeter p_meter = new PullableMeter(p.getPullableOutput(index), reference, original_id, index);
		return p_meter;
	}

	public class PushableMeter extends PushableWrapper
	{
		int m_index = 0;

		int m_originalId = 0;

		PushableMeter(Pushable p, Processor reference, int original_id, int index)
		{
			super(p, reference);
			m_index = index;
			m_originalId = original_id;
		}

		@Override
		synchronized public Pushable push(Object o)
		{
			long time_start = System.nanoTime();
			m_pushable.push(o);
			long time_end = System.nanoTime();
			long duration = time_end - time_start;
			Map<Integer,Long> counts = m_inputPushCount.get(m_originalId);
			counts.put(m_index, counts.get(m_index) + 1);
			m_inputPushCount.put(m_originalId, counts);
			Map<Integer,Long> durations = m_inputTotalTime.get(m_originalId);
			durations.put(m_index, durations.get(m_index) + duration);
			m_inputTotalTime.put(m_originalId, durations);
			return this;
		}
	}

	public  class PullableMeter extends PullableWrapper
	{
		int m_index = 0;

		int m_originalId = 0;

		PullableMeter(Pullable p, Processor reference, int original_id, int index)
		{
			super(p, reference);
			m_index = index;
			m_originalId = original_id;
		}

		@Override
		synchronized public NextStatus hasNextSoft()
		{
			long time_start = System.nanoTime();
			NextStatus s = m_pullable.hasNextSoft();
			long time_end = System.nanoTime();
			long duration = time_end - time_start;
			Map<Integer,Long> counts = m_outputPullCount.get(m_originalId);
			counts.put(m_index, counts.get(m_index) + 1);
			m_outputPullCount.put(m_originalId, counts);
			Map<Integer,Long> durations = m_outputTotalTime.get(m_originalId);
			durations.put(m_index, durations.get(m_index) + duration);
			m_outputTotalTime.put(m_originalId, durations);
			return s;
		}

		@Override
		synchronized public boolean hasNext()
		{
			long time_start = System.nanoTime();
			boolean s = m_pullable.hasNext();
			long time_end = System.nanoTime();
			long duration = time_end - time_start;
			Map<Integer,Long> durations = m_outputTotalTime.get(m_originalId);
			durations.put(m_index, durations.get(m_index) + duration);
			m_outputTotalTime.put(m_originalId, durations);
			return s;
		}

		@Override
		synchronized public Object pull()
		{
			Object o = m_pullable.pull();
			if (o != null)
			{
				Map<Integer,Long> counts = m_outputPullCount.get(m_originalId);
				counts.put(m_index, counts.get(m_index) + 1);
				m_outputPullCount.put(m_originalId, counts);
			}
			return o;
		}

		@Override
		synchronized public Object pullSoft()
		{
			Object o = m_pullable.pullSoft();
			if (o != null)
			{
				Map<Integer,Long> counts = m_outputPullCount.get(m_originalId);
				counts.put(m_index, counts.get(m_index) + 1);
				m_outputPullCount.put(m_originalId, counts);
			}
			return o;
		}
	}
}
