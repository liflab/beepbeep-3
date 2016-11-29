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
package ca.uqac.lif.cep;

public class ProcessorWrapper extends Processor
{
	/**
	 * The processor being wrapped around
	 */
	protected Processor m_processor;
	
	/**
	 * Creates a new processor wrapper
	 * @param p The processor being wrapped around
	 */
	public ProcessorWrapper(Processor p)
	{
		super(p.getInputArity(), p.getOutputArity());
		m_processor = p;
	}

	@Override
	public Pushable getPushableInput(int index)
	{
		Pushable p = m_processor.getPushableInput(index);
		return new PushableWrapper(p, this);
	}

	@Override
	public Pullable getPullableOutput(int index) 
	{
		Pullable p = m_processor.getPullableOutput(index);
		return new PullableWrapper(p, this);
	}
	
	@Override
	public void setPullableInput(int index, Pullable p)
	{
		Pullable new_p = new PullableWrapper(p, this);
		m_processor.setPullableInput(index, new_p);
	}
	
	@Override
	public void setPushableOutput(int index, Pushable p)
	{
		Pushable new_p = new PushableWrapper(p, this);
		m_processor.setPushableOutput(index, new_p);
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
	public Processor clone() 
	{
		ProcessorWrapper pw = new ProcessorWrapper(m_processor.clone());
		cloneInto(pw);
		return pw;
	}
	
	protected void cloneInto(ProcessorWrapper pw)
	{
		pw.setContext(m_context);
	}
}
