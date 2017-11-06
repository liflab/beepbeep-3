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
package ca.uqac.lif.cep.cli;

import java.util.Queue;
import java.util.ArrayDeque;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.tmf.Sink;
import ca.uqac.lif.cep.util.AnsiPrinter;

/**
 * Sends its input to an {@link ca.uqac.lif.cep.util.AnsiPrinter ANSI printer}
 * (such as the standard output). This processor takes whatever event it
 * receives (i.e. any Java <tt>Object</tt>), calls its {@link Object#toString()
 * toString()} method, and pushes the resulting output to the computer's
 * standard output. Graphically, it is represented as:
 * <p>
 * <a href="{@docRoot}/doc-files/cli/Print.png"><img
 *   src="{@docRoot}/doc-files/cli/Print.png"
 *   alt="Processor graph"></a>
 * <p>
 * The behaviour of this processor can be configured in a few ways. Methods
 * {@link #setPrefix(String) setPrefix()} and {@link #setPrefix(String) setSuffix()}
 * can specify the character string to be displayed before and after each
 * event, and method {@link #setSeparator(String) setSeparator()} defines the
 * symbol that is inserted between each event. Further customization of the
 * output can be achieved by obtaining a reference to the underlying ANSI
 * printer using {@link getAnsiPrinter()}.
 * 
 * @author Sylvain Hallé
 */
public class Print extends Sink
{
	/**
	 * The stream to print to
	 */
	protected AnsiPrinter m_out;
	
	/**
	 * The separator between each event
	 */
	protected String m_separator = ",";
	
	/**
	 * The prefix to display before each event
	 */
	protected String m_prefix = "";
	
	/**
	 * The suffix to display after each event
	 */
	protected String m_suffix = "";

	/**
	 * Creates a new printer
	 */
	@SuppressWarnings("squid:S106")
	public Print()
	{
		this(1, new AnsiPrinter(System.out));
	}
	
	public Print(String separator)
	{
		this();
		m_separator = separator;
	}

	/**
	 * Creates a new ANSI printer of given input arity
	 * @param in_arity The input arity
	 * @param out The ANSI printer to use
	 */
	public Print(int in_arity, AnsiPrinter out)
	{
		super(in_arity);
		m_out = out;
	}
	
	/**
	 * Sets a prefix to display before each event
	 * @param prefix The prefix; can be any string and include ANSI
	 * escape sequences
	 * @return This print processor
	 */
	public /*@NotNull*/ Print setPrefix(/*@NotNull*/ String prefix)
	{
		m_prefix = prefix;
		return this;
	}
	
	/**
	 * Sets a suffix to display before each event. This is not the same
	 * thing as the separator that can be set with {@link #setSeparator(String)
	 * setSeparator()}. The suffix is appended immediately after each event,
	 * while the separator is appended only after the next event arrives.
	 * @param suffix The suffix; can be any string and include ANSI
	 * escape sequences
	 * @return This print processor
	 */
	public /*@NotNull*/ Print setSuffix(/*@NotNull*/ String suffix)
	{
		m_prefix = suffix;
		return this;
	}
	
	/**
	 * Sets a separator to display after each event. This is not the same
	 * thing as the separator that can be set with {@link #setSeparator(String)
	 * setSeparator()}
	 * @param separator The separator; can be any string and include ANSI
	 * escape sequences
	 * @return This print processor
	 */
	public /*@NotNull*/ Print setSeparator(/*@NotNull*/ String separator)
	{
		m_separator = separator;
		return this;
	}
	
	/**
	 * Enables or disables the display of colors in the resulting output.
	 * This has for effect of enabling/disabling the use of ANSI escape
	 * sequences in the underlying ANSI printer object.
	 * @param b Set to {@code true} to enable colors, {@code false} otherwise
	 * @return This print processor
	 */
	public Print setAnsi(boolean b)
	{
		if (b)
		{
			m_out.enableColors();
		}
		else
		{
			m_out.disableColors();
		}
		return this;
	}
	
	/**
	 * Gets a reference to the ANSI printer to which the
	 * character strings will be sent.
	 * @return The ANSI printer
	 */
	public /*@NotNull*/ AnsiPrinter getAnsiPrinter()
	{
		return m_out;
	}
	
	/**
	 * Sets the ANSI printer to which the character string will be sent.
	 * @param printer The ANSI printer
	 * @return This Print processor
	 */
	public Print setAnsiPrinter(/*@NotNull*/ AnsiPrinter printer)
	{
		m_out = printer;
		return this;
	}
	
	@Override
	@SuppressWarnings("squid:S1168")
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		if (inputs == null || allNull(inputs))
		{
			return false;
		}
		Object o = inputs[0];
		if (o != null)
		{
			m_out.setForegroundColor(AnsiPrinter.Color.LIGHT_GRAY);
			prettyPrint(m_prefix + o);
			m_out.setForegroundColor(AnsiPrinter.Color.RED);
			m_out.print(m_separator);
		}
		return true;
	}

	@SuppressWarnings("squid:S106")
	public static void build(ArrayDeque<Object> stack) throws ConnectorException
	{
		Processor p = (Processor) stack.pop();
		stack.pop(); // PRINT
		Print out = new Print(1, new AnsiPrinter(System.out));
		Connector.connect(p, out);
		stack.push(out);
	}

	/**
	 * Prints an object in an eye-pleasing way
	 * @param o The object
	 */
	protected void prettyPrint(/*@NotNull*/ Object o)
	{
		if (o instanceof Number)
		{
			prettyPrint((Number) o);
		}
		else
		{
			m_out.print(o);
		}
	}

	/**
	 * Prints a number in an eye-pleasing way. In this case, the
	 * printer trims the decimals from a number if it is an integer
	 * @param n The number
	 */
	protected void prettyPrint(/*@NotNull*/ Number n)
	{
		if (n.floatValue() == Math.round(n.floatValue()))
		{
			m_out.print(n.intValue());
		}
		else
		{
			m_out.print(n);
		}
	}

	@Override
	public /*@NotNull*/ Print clone()
	{
		return new Print(getInputArity(), m_out);
	}
}
