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
package ca.uqac.lif.cep.io;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * Utility class to run commands on the command line and fetch their
 * output.
 * @author Sylvain Hallé
 *
 */
public class CommandRunner extends Thread
{
	protected String[] m_command;

	protected byte[] m_stdin;

	protected volatile boolean m_stop = false;

	protected StreamGobbler m_stdoutGobbler;

	protected StreamGobbler m_stderrGobbler;

	protected int m_errorCode = 0;

	/**
	 * Creates a CommandRunner to run a command.
	 * @param command The command to run
	 * @param stdin If not set to null, this array of bytes
	 * will be sent to the stdin of the command being run
	 */
	public CommandRunner(String[] command, byte[] stdin)
	{
		super();
		m_command = command;
		m_stdin = stdin;
	}

	/**
	 * Creates a CommandRunner to run a command.
	 * @param command The command to run
	 * @param stdin If not set to null, this string will be sent to the stdin
	 *   of the command being run
	 */
	public CommandRunner(String[] command, String stdin)
	{
		this(command, stdin.getBytes());
	}

	/**
	 * Creates a CommandRunner to run a command.
	 * @param command The command to run
	 */
	public CommandRunner(String[] command)
	{
		this(command, new byte[0]);
	}

	/**
	 * Constantly reads an input stream and captures its content.
	 * Inspired from <a href="http://stackoverflow.com/questions/14165517/processbuilder-forwarding-stdout-and-stderr-of-started-processes-without-blocki">ArrayDeque Overflow</a>
	 */
	protected class StreamGobbler extends Thread
	{
		InputStream m_is;
		ArrayList<Byte> m_contents;
		String m_name;

		private StreamGobbler(InputStream is, String name)
		{
			super();
			m_contents = new ArrayList<Byte>();
			this.m_is = is;
			m_name = name;
		}

		@Override
		public void run()
		{
			try
			{
				byte[] buffer = new byte[8192];
				int len;
				while (!m_stop && (len = m_is.read(buffer)) > 0)
				{
					synchronized (this)
					{
						for (int i = 0; i < len; i++)
						{
							m_contents.add(buffer[i]);
						}
					}
				}
				m_is.close();
			}
			catch (IOException ioe)
			{
				Logger.getAnonymousLogger().log(Level.WARNING, "", ioe);
			}
		}

		/**
		 * Returns the contents captured by the gobbler as an array of bytes
		 * @return The contents
		 */
		public synchronized byte[] getBytes()
		{
			int size = m_contents.size();
			byte[] out = new byte[size];
			int i = 0;
			for (byte b : m_contents)
			{
				out[i++] = b;
			}
			return out;
		}
	}

	public static byte[] runAndGet(String[] command, String inputs) throws IOException
	{
		return runAndGet(command, inputs.getBytes());
	}

	public static byte[] runAndGet(String[] command, byte[] inputs) throws IOException
	{
		CommandRunner runner = new CommandRunner(command, inputs);
		runner.execute();
		// Wait until the command is done
		while (runner.isAlive())
		{
			// Wait 0.1 s and check again
			try
			{
				Thread.sleep(100);
			}
			catch (InterruptedException e)
			{
				// This happens if the user cancels the command manually
				runner.stopCommand();
				runner.interrupt();
				return new byte[0];
			}
		}
		return runner.getBytes();
	}

	@Override
	public void run()
	{
		try
		{
			execute();
		}
		catch (IOException e)
		{
			Logger.getAnonymousLogger().log(Level.WARNING, "", e);
		}
	}

	protected void execute() throws IOException
	{
		Process process = null;
		try
		{
			ProcessBuilder builder = new ProcessBuilder(m_command);
			process = builder.start();
			m_stderrGobbler = new StreamGobbler(process.getErrorStream(), "ERR");
			m_stdoutGobbler = new StreamGobbler(process.getInputStream(), "IN");
			// Send data into stdin of process
			if (m_stdin != null)
			{
				OutputStream process_stdin = process.getOutputStream();
				process_stdin.write(m_stdin, 0, m_stdin.length);
				process_stdin.flush();
				process_stdin.close();
			}
			// Start gobblers
			m_stderrGobbler.start();
			m_stdoutGobbler.start();
			m_errorCode = process.waitFor();
			do
			{
				// Wait for both gobblers to finish
			} while (!m_stop && (m_stderrGobbler.isAlive() || m_stdoutGobbler.isAlive()));
		}
		catch (InterruptedException e)
		{
			// Destroy the running command
			process.destroy();
			Thread.currentThread().interrupt();
		}
	}

	/**
	 * Gets the contents of stdout sent by the command as an array of bytes
	 * @return The contents of stdout
	 */
	public synchronized byte[] getBytes()
	{
		return m_stdoutGobbler.getBytes();
	}

	/**
	 * Gets the contents of stdout sent by the command as a string
	 * @return The contents of stdout
	 */
	public synchronized String getString()
	{
		byte[] out = m_stdoutGobbler.getBytes();
		return new String(out);
	}

	public synchronized void stopCommand()
	{
		m_stop = true;
	}

}
