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
package ca.uqac.lif.cep.gnuplot;

import java.util.Queue;

import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.sets.EmlBag;
import ca.uqac.lif.util.CommandRunner;

public abstract class GnuplotProcessor extends SingleProcessor 
{
	/**
	 * The graph's title
	 */
	protected String m_title;
	
	/**
	 * The terminal used for the plot's output
	 */
	public static enum Terminal {PDF, PNG, GIF, SVG, JPEG};

	/**
	 * The default terminal to use if none is specified
	 */
	public static final Terminal DEFAULT_TERMINAL = Terminal.PNG;
	
	/**
	 * The terminal used to display the plot
	 */
	protected String m_terminal;
	
	/**
	 * The string containing the last plot generated
	 */
	protected String m_lastPlot;
	
	/**
	 * Whether to output the raw (text) data, or the <em>image</em> resulting
	 * from running the Gnuplot command on that data
	 */
	protected boolean m_isRaw = false;
	
	/**
	 * The path to launch GnuPlot
	 */
	protected static String s_path = "gnuplot";
	
	/**
	 * The time to wait (in milliseconds) before polling GnuPlot's result 
	 */
	protected static long s_waitInterval = 100;
	
	public GnuplotProcessor()
	{
		super(1, 1);
		m_terminal = getTerminalString(DEFAULT_TERMINAL);
	}
	
	/**
	 * Sets the graph's title.
	 * @param title The title
	 * @return An instance of this GnuPlot object
	 */
	public GnuplotProcessor setTitle(String title)
	{
		if (title != null)
		{
			m_title = title;
		}
		return this;
	}
	
	/**
	 * Sets the path to run the GnuPlot executable
	 * @param path The path
	 * @return An instance of this GnuPlot object
	 */
	public GnuplotProcessor setPath(String path)
	{
		s_path = path;
		return this;
	}
	
	/**
	 * Sets whether the processor should output a data file or
	 * an image
	 * @param raw Set to <code>true</code> to output the raw (text) data,
	 * rather than the <em>image</em> resulting
	 * from running the Gnuplot command on that data
	 * @return An instance of this GnuPlot object
	 */
	public GnuplotProcessor setRaw(boolean raw)
	{
		m_isRaw = raw;
		return this;
	}
	
	protected abstract StringBuilder computePlot(EmlBag bag);
	
	@Override
	protected final Queue<Object[]> compute(Object[] inputs) 
	{
		Object first_input = inputs[0];
		if (first_input instanceof EmlBag)
		{
			EmlBag bag = (EmlBag) first_input;
			StringBuilder plot_contents = computePlot(bag);
			m_lastPlot = plot_contents.toString();
		}
		if (m_isRaw)
		{
			return wrapObject(m_lastPlot);
		}
		byte[] image = getImage(m_lastPlot);
		return wrapObject(image);
	}
	
	/**
	 * Sets the terminal (i.e. the file type) for the graph
	 * @param t The terminal
	 * @return An instance of this processor
	 */
	public GnuplotProcessor setTerminal(Terminal t)
	{
		m_terminal = getTerminalString(t);
		return this;
	}
	
	/**
	 * Runs Gnuplot on a file and returns the resulting graph
	 * @param instructions The text file for this Gnuplot
	 * @return The (binary) contents of the image produced by Gnuplot
	 */
	public final byte[] getImage(String instructions)
	{
		byte[] image = null;
		String[] command = {s_path};
		CommandRunner runner = new CommandRunner(command, instructions);
		runner.start();
		// Wait until the command is done
		while (runner.isAlive())
		{
			// Wait 0.1 s and check again
			try
			{
				Thread.sleep(s_waitInterval);
			}
			catch (InterruptedException e) 
			{
				// This happens if the user cancels the command manually
				runner.stopCommand();
				runner.interrupt();
				return null;
			}
		}
		image = runner.getBytes();
		return image;
	}
	
	/**
	 * Returns the terminal string associated to this plot 
	 * @param term The terminal
	 * @return A string understood by Gnuplot for the terminal's name
	 */
	public static String getTerminalString(Terminal term)
	{
		String out = "";
		switch (term)
		{
		case GIF:
			out = "gif";
			break;
		case PDF:
			out = "pdf";
			break;
		case PNG:
			out = "png";
			break;
		case SVG:
			out = "svg";
			break;
		case JPEG:
			out = "jpg";
			break;
		default:
			break;
		}
		return out;
	}

	public static Terminal stringToTerminal(String s)
	{
		s = s.trim();
		if (s.compareToIgnoreCase("png") == 0)
		{
			return Terminal.PNG;
		}
		if (s.compareToIgnoreCase("gif") == 0)
		{
			return Terminal.GIF;
		}
		if (s.compareToIgnoreCase("pdf") == 0)
		{
			return Terminal.PDF;
		}
		if (s.compareToIgnoreCase("svg") == 0)
		{
			return Terminal.SVG;
		}
		if (s.compareToIgnoreCase("jpg") == 0)
		{
			return Terminal.JPEG;
		}
		return DEFAULT_TERMINAL;
	}
}
