/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2023 Sylvain Hallé

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

import ca.uqac.lif.cep.ProcessorException;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.tmf.Source;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Queue;

/**
 * Read contents from a Java {@link InputStream}, and outputs its chunks as
 * byte arrays. It is represented graphically as:
 * <p>
 * <img src="{@docRoot}/doc-files/io/StreamReader.png" alt="ReadInputStream">
 * <p>
 * If the processor is instantiated by passing it a {@link File}, the processor
 * attempts to auto-detect if it is a "regular" file or a named pipe. In the
 * latter case, the processor will keep trying to fetch bytes from the input
 * stream until the "end of transmission" (EOT) byte is observed.
 * 
 * @author Sylvain Hallé
 * @since 0.7
 */
public class ReadInputStream extends Source
{
	/**
	 * The input stream this processor is reading from
	 */
	protected InputStream m_inputStream;

	/**
	 * A reader to wrap around this input stream
	 */
	protected transient InputStreamReader m_inputStreamReader;

	/**
	 * A buffered reader to wrap around the input stream
	 */
	protected transient BufferedReader m_br;

	/**
	 * Creates a new input stream processor
	 * 
	 * @param is
	 *          The input stream to read from
	 */
	public ReadInputStream(InputStream is)
	{
		super(1);
		m_inputStream = is;
		m_inputStreamReader = new InputStreamReader(is);
		m_br = new BufferedReader(m_inputStreamReader);
	}

	/**
	 * Creates a new input stream processor, by opening an input stream on a
	 * file object.
	 * @param f The file to read from
	 * @throws FileNotFoundException Thrown if the file does not exist
	 */
	public ReadInputStream(File f) throws FileNotFoundException
	{
		this(new FileInputStream(f));
		m_isFile = f.isFile();
	}

	/**
	 * Character indicating the closing of a pipe. By default, we use ASCII 4, which
	 * is traditionally interpreted as the
	 * <a href="http://en.wikipedia.org/wiki/End-of-transmission_character">end of
	 * transmission character (EOT)</a>. This has no effect when the underlying
	 * input is not a pipe.
	 */
	public static final transient char END_CHARACTER = (char) 4;

	/**
	 * The size of chunks. The processor will try to read this number of bytes every
	 * time it queries the underlying input stream. Setting it to a too small value
	 * will cause the reader to loop uselessly to process tiny bits of the string.
	 * Setting it to a too large value (i.e. 1 MB) has an equally adverse effect.
	 * Experimentally, a sweet spot seems to be 16 kB.
	 */
	protected int m_chunkSize = 16384;

	/**
	 * Whether the input stream to read is connected to a file. This matters when
	 * attempting to read from the stream fails. If the source is a file, this means
	 * the file is over. Otherwise, it simply means there is no data ready to be
	 * read right now.
	 */
	protected boolean m_isFile = true;

	/**
	 * Whether the EOT character has been received
	 */
	protected boolean m_hasReadEot = false;

	/**
	 * Sets the size of chunks (in bytes) that the stream reader will try to read
	 * from the source at each attempt.
	 * 
	 * @param size
	 *          The size, in bytes. Must be greater than 0.
	 * @return This stream reader
	 */
	public ReadInputStream setChunkSize(int size)
	{
		m_chunkSize = size;
		return this;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		if (m_hasReadEot)
		{
			// We received EOT previously: no more output to produce
			return false;
		}
		try
		{
			if (m_br.ready())
			{
				char[] char_array = new char[m_chunkSize];
				int chars_read = m_br.read(char_array, 0, m_chunkSize);
				// When the input is a pipe and we read the special character,
				// this indicates the end of transmission
				if (chars_read > 0)
				{
					char[] new_array = Arrays.copyOf(char_array, chars_read);
					char[] out_array;
					if (!m_isFile && new_array[new_array.length - 1] == END_CHARACTER)
					{
						// We don't read a file, but the input stream
						// has the EOT character: trim this EOT form the output
						out_array = Arrays.copyOf(new_array, chars_read - 1);
						// And remember this stream is over
						m_hasReadEot = true;
						m_br.close();
					}
					else
					{
						out_array = new_array;
					}
					outputs.add(new Object[] { out_array });
					return !m_hasReadEot;
				}
			}
			else
			{
				// If the underlying input source is not a pipe, the
				// fact that the input stream is not ready means there
				// is no more data to read.
				if (m_isFile)
				{
					return false;
				}
			}
			// At this point, we haven't read bytes, but we don't know if we'll
			// be able to read some in the future: return true just in case
			return true;
		}
		catch (IOException e)
		{
			throw new ProcessorException(e);
		}
	}

	/**
	 * Tells this reader whether it is reading from a file or some other input
	 * source.
	 * 
	 * @param b
	 *          Set to {@code true} to tell the reader it is reading a file,
	 *          {@code false} otherwise
	 * @return This stream reader
	 */
	public ReadInputStream setIsFile(boolean b)
	{
		m_isFile = b;
		return this;
	}

	@Override
	public ReadInputStream duplicate(boolean with_state)
	{
		// By default, it does not make sense to duplicate such a processor
		throw new UnsupportedOperationException();
	}

	@Override
	public Pullable getPullableOutput(int index)
	{
		// Override method from SynchronousProcessor, to give a
		// ReadInputStreamPullable instead of a normal OutputPullable
		if (m_outputPullables[index] == null)
		{
			m_outputPullables[index] = new ReadInputStreamPullable(index);
		}
		return m_outputPullables[index];
	}

	/**
	 * A special {@link Pullable} that overrides the default behavior of
	 * {@link ca.uqac.lif.cep.SynchronousProcessor.OutputPullable
	 * SynchronousProcessor.OutputPullable}. Normally, a call to
	 * {@link #hasNext()} asks the processor for a new output event, and if no
	 * event is produced, the process is repeated a fixed number of times,
	 * after which it is concluded that the processor will never produce any
	 * new event. This does not work when reading bytes from a named pipe,
	 * where the appropriate behavior is to wait forever because new
	 * bytes to read may always become available in the future.
	 */
	protected class ReadInputStreamPullable extends OutputPullable
	{
		public ReadInputStreamPullable(int index)
		{
			super(index);
		}

		@Override
		public boolean hasNext()
		{
			if (m_isFile)
			{
				return super.hasNext();
			}
			// If named pipe, wait until hasNextSoft has
			// answered either YES or NO; otherwise loop forever
			Queue<Object> out_queue = m_outputQueues[getPosition()];
			// If an event is already waiting in the output queue,
			// return it and don't pull anything from the input
			if (!out_queue.isEmpty())
			{
				return true;
			}
			// Next line is different from OutputPullable, which has a bounded for loop
			while (true)
			{
				for (int i = 0; i < m_inputArity; i++)
				{
					Pullable p = m_inputPullables[i];
					if (p == null)
					{
						throw new PullableException("Input " + i + " of processor " + ReadInputStream.this
								+ " is connected to nothing", getProcessor());
					}
					boolean status = p.hasNext();
					if (!status)
					{
						if (allNotifiedEndOfTrace())
						{
							return false;
						}
						Queue<Object[]> last_queue = new ArrayDeque<Object[]>();
						boolean b = onEndOfTrace(last_queue);
						m_hasBeenNotifiedOfEndOfTrace[i] = true;
						if (!b)
						{
							return false;
						}
						for (Object[] front : last_queue)
						{
							for (int j = 0; j < m_outputArity; j++)
							{
								m_outputQueues[j].add(front[j]);
							}
						}
						return true;
					}
				}
				// We are here only if every input pullable has answered YES
				// Pull an event from each
				Object[] inputs = new Object[m_inputArity];
				for (int i = 0; i < m_inputArity; i++)
				{
					Pullable p = m_inputPullables[i];
					// Don't check for p == null, we did it above
					Object o = p.pull();
					inputs[i] = o;
				}
				// Compute output event(s)
				m_tempQueue.clear();
				boolean computed;
				try
				{
					computed = compute(inputs, m_tempQueue);
				}
				catch (ProcessorException e)
				{
					throw new PullableException(e);
				}
				NextStatus status_to_return = NextStatus.NO;
				if (!computed && m_tempQueue.isEmpty())
				{
					// No output will ever be returned: stop there
					return false;
				}
				if (!m_tempQueue.isEmpty())
				{
					// We computed an output event; add it to the output queue
					// and answer YES
					for (Object[] evt : m_tempQueue)
					{
						if (evt != null)
						{
							for (int i = 0; i < m_outputArity; i++)
							{
								Queue<Object> queue = m_outputQueues[i];
								queue.add(evt[i]);
							}
							status_to_return = NextStatus.YES;
						}
						else
						{
							// This source will NEVER output anything again
							m_tempQueue.clear();
							return false;
						}
					}
					if (status_to_return == NextStatus.YES)
					{
						m_tempQueue.clear();
						return true;
					}
				}
				// Otherwise, try the whole thing again
			}
		}
	}
}
