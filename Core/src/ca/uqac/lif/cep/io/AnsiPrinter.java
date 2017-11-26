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
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.logging.Level;

import ca.uqac.lif.cep.util.BeepBeepLogger;

/**
 * Print stream with facilities for producing colored text using
 * ANSI escape codes.
 * @author sylvain
 */
public class AnsiPrinter extends PrintStream
{
	/**
	 * Default 16-color scheme for foreground and background text
	 */
	public static enum Color {BLACK, BLUE, GREEN, CYAN, RED, PURPLE, BROWN,
		LIGHT_GRAY, DARK_GRAY, LIGHT_BLUE, LIGHT_GREEN, LIGHT_CYAN, LIGHT_RED,
		LIGHT_PURPLE, YELLOW, WHITE}

	/**
	 * Whether ANSI codes are enabled. If set to false (with
	 * {@link #disableColors()}), behaves like a normal PrintStream
	 */
	protected boolean m_enabled = true;

	/**
	 * Instantiates an AnsiPrinter.
	 * @param out The OutputStream where the printer will send its output
	 */
	public AnsiPrinter(OutputStream out)
	{
		super(out);
	}

	/**
	 * Enables the output of ANSI codes in the output stream
	 */
	public void enableColors()
	{
		m_enabled = true;
	}

	/**
	 * Disables the output of ANSI codes in the output stream
	 */
	public void disableColors()
	{
		m_enabled = false;
	}

	/**
	 * Sets the foreground color for printed text.
	 * Until this color is changed, the text will be printed using
	 * that color.
	 * @param c The color
	 */
	public void setForegroundColor(AnsiPrinter.Color c)
	{
		if (!m_enabled)
		{
			return;
		}
		String to_print = "";
		switch (c)
		{
		case BLACK:
			to_print = "\u001B[0;30m";
			break;
		case RED:
			to_print = "\u001B[0;31m";
			break;
		case GREEN:
			to_print = "\u001B[0;32m";
			break;
		case BROWN:
			to_print = "\u001B[0;33m";
			break;
		case BLUE:
			to_print = "\u001B[0;34m";
			break;
		case PURPLE:
			to_print = "\u001B[0;35m";
			break;
		case CYAN:
			to_print = "\u001B[0;36m";
			break;
		case LIGHT_GRAY:
			to_print = "\u001B[0;37m";
			break;
		case DARK_GRAY:
			to_print = "\u001B[1;30m";
			break;
		case LIGHT_RED:
			to_print = "\u001B[1;31m";
			break;
		case LIGHT_GREEN:
			to_print = "\u001B[1;32m";
			break;
		case YELLOW:
			to_print = "\u001B[1;33m";
			break;
		case LIGHT_BLUE:
			to_print = "\u001B[1;34m";
			break;
		case LIGHT_PURPLE:
			to_print = "\u001B[1;35m";
			break;
		case LIGHT_CYAN:
			to_print = "\u001B[1;36m";
			break;
		case WHITE:
			to_print = "\u001B[1;37m";
			break;
		default:
			// Do nothing
			break;
		}
		try
		{
			out.write(to_print.getBytes());
		}
		catch (IOException e)
		{
			BeepBeepLogger.logger.log(Level.WARNING, "", e);
		}
	}

	/**
	 * Resets the colors to their default values
	 */
	public void resetColors()
	{
		setForegroundColor(Color.LIGHT_GRAY);
	}

}
