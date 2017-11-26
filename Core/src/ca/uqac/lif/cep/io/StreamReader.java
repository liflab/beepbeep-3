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
package ca.uqac.lif.cep.io;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.UnsupportedEncodingException;
import java.util.Queue;
import java.util.logging.Level;

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.tmf.Source;
import ca.uqac.lif.cep.util.BeepBeepLogger;

/**
 * Reads chunks of data from an input source.
 * These chunks are returned as events in the form of strings.
 * 
 * @author Sylvain Hallé
 */
public class StreamReader extends Source
{
	/**
	 * The input stream from which data will be read
	 */
	protected InputStream m_fis = null;

	/**
	 * The size of chunks. The PipeReader will try to read this number
	 * of bytes every time it queries the underlying input source.
	 * Setting it to a too small value will cause the reader to loop
	 * uselessly to process tiny bits of the string. Setting it to a
	 * too large value (i.e. 1 MB) has an equally adverse effect.
	 * Experimentally, a sweet spot seems to be 16 kB.
	 */
	protected static final int s_chunkSize = 16384;

	/**
	 * The interval that the reader should sleep
	 * (i.e. wait) before polling the pipe again in the loop.
	 * This interval is broken down in milliseconds + nanoseconds;
	 * nano should not be over 999,999 (otherwise add 1 to milli).
	 * You should tweak these values to avoid clogging your CPU
	 * (setting them to 0 will hike it to 100%) while not lagging
	 * on the input trace.
	 */
	protected int m_sleepIntervalMs = 0;
	protected int m_sleepIntervalNs = 100000;

	/**
	 * Character indicating the closing of a pipe.
	 * By default, we use ASCII 4, which is traditionally interpreted
	 * as the <a href="http://en.wikipedia.org/wiki/End-of-transmission_character">end
	 * of transmission character (EOT)</a>. This has no effect when the
	 * underlying input is not a pipe.
	 */
	public static final String END_CHARACTER = String.valueOf((char) 4);

	/**
	 * Remembers whether the underlying input stream is a file or
	 * a pipe. This changes the condition to test to determine
	 * if there is more data to read.
	 */
	protected boolean m_isFile;

	/**
	 * The pipe reader carries a "return code" that indicates
	 * under which conditions the thread has stopped (normal
	 * end or error of some kind)
	 */
	protected int m_returnCode;
	public static final int ERR_OK = 0;
	public static final int ERR_THREAD = 1;
	public static final int ERR_EOF = 2;  // Encountered EOF (for a file)
	public static final int ERR_EOT = 3;  // Encountered EOT (for a pipe)

	protected BufferedReader m_br;

	protected InputStreamReader m_isr;
	
	protected StreamListener m_listener;

	/**
	 * Determines whether the reader operates in "pull" or "push" mode
	 */
	protected boolean m_pushMode = false;

	public StreamReader()
	{
		super(1);
	}

	public StreamReader(InputStream is)
	{
		super(1);
		m_returnCode = ERR_OK;
		m_isFile = true;
		setInputStream(is);
	}

	/**
	 * Sets the input stream to read from
	 * @param is The input stream to read from
	 */
	public void setInputStream(InputStream is)
	{
		m_fis = is;
		if (m_fis != null)
		{
			try
			{
				m_isr = new InputStreamReader(is, "UTF8");
				m_br = new BufferedReader(m_isr);
			}
			catch (UnsupportedEncodingException e)
			{
				BeepBeepLogger.logger.log(Level.SEVERE, "", e);
			}
		}
	}

	/**
	 * Sets whether this stream reader works in pull or push mode
	 * @param b Set to {@code true} for push mode, {@code false} for pull mode
	 * @return This stream reader
	 */
	public StreamReader setPushMode(boolean b)
	{
		m_pushMode = b;
		return this;
	}

	/**
	 * Tells the reader whether the input source is a pipe or a
	 * regular file.
	 * @param b Set to true if source is a file; false otherwise
	 * @return This stream reader
	 */
	public StreamReader setIsFile(boolean b)
	{
		m_isFile = b;
		return this;
	}

	public int getReturnCode()
	{
		return m_returnCode;
	}

	@Override
	@SuppressWarnings({"squid:S1168", "squid:S1166"})
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		String s_read = readString();
		if (m_returnCode == ERR_EOF || m_returnCode == ERR_EOT)
		{
			// End of stream
			return false;
		}
		outputs.add(new Object[]{s_read});
		return true;
	}
	
	protected String readString()
	{
		try
		{
			if (m_br.ready())
			{
				char[] char_array = new char[s_chunkSize];
				int chars_read = m_br.read(char_array, 0, s_chunkSize);
				// When the input is a pipe and we read the special character,
				// this indicates the end of transmission
				if (!m_isFile)
				{
					String st = new String(char_array);
					if (st.contains(END_CHARACTER))
					{
						m_returnCode = ERR_EOT;
					}
				}
				if (chars_read > 0)
				{
					return new String(char_array).substring(0, chars_read - 1);
				}
			}
			else
			{
				// If the underlying input source is not a pipe, the
				// fact that the input stream is not ready means there
				// is no more data to read.
				if (m_isFile)
				{
					m_returnCode = ERR_EOF;
				}
			}
		}
		catch (IOException e)
		{
			// This will occur if the input stream is closed
			// Not an error in itself, but will cause the thread in which PipeReader
			// runs to end (gracefully)
		}
		return null;
	}

	@Override
	public StreamReader duplicate()
	{
		return new StreamReader(m_fis);
	}

	@Override
	public void start() throws ProcessorException
	{
		m_listener = new StreamListener();
		Thread t = new Thread(m_listener);
		t.start();
	}
	
	@Override
	public void stop() throws ProcessorException
	{
		if (m_listener != null)
		{
			m_listener.stop();
		}
	}

	protected class StreamListener implements Runnable
	{
		protected volatile boolean m_run;

		@Override
		public void run()
		{
			m_run = true;
			Pushable p = StreamReader.this.getPushableOutput(0);
			while (m_run)
			{
				String s = readString();
				if (s != null)
				{
					p.push(s);
				}
				try
				{
					Thread.sleep(m_sleepIntervalMs, m_sleepIntervalNs);
				}
				catch (InterruptedException e) 
				{
					// Restore interrupted state
					Thread.currentThread().interrupt();
				}
			}
		}
		
		public void stop()
		{
			m_run = false;
		}
	}
}
