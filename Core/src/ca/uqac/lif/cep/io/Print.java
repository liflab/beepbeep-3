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

import ca.uqac.lif.cep.tmf.Sink;
import java.io.PrintStream;
import java.util.Queue;

/**
 * Sends its input to a PrintStream (such as the standard output). This
 * processor takes whatever event it receives (i.e. any Java {@code Object}),
 * calls its {@link Object#toString() toString()} method, and pushes the
 * resulting output to a print stream. Graphically, it is represented as:
 * <p>
 * <img src="{@docRoot}/doc-files/cli/Print.png" alt="Print">
 * <p>
 * The behaviour of this processor can be configured in a few ways. Methods
 * {@link #setPrefix(String) setPrefix()} and {@link #setPrefix(String)
 * setSuffix()} can specify the character string to be displayed before and
 * after each event, and method {@link #setSeparator(String) setSeparator()}
 * defines the symbol that is inserted between each event. Further customization
 * of the output can be achieved by passing to a fancier type of print stream,
 * such as an ANSI-aware printer.
 * 
 * @author Sylvain Hallé
 * @since 0.1
 */
@SuppressWarnings("squid:S2160")
public class Print extends Sink
{
	/**
	 * The stream to print to
	 */
	protected transient PrintStream m_out;

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
	 * A flag determining if the printed token is the first. This flag is used to
	 * avoid printing a dangling separator token after the last printed token.
	 * The separator is printed only if another token comes after it.
	 */
	protected boolean m_firstOut;

	/**
	 * Creates a new printer with an input arity of 1 and sending its output to the
	 * standard output.
	 */
	@SuppressWarnings("squid:S106")
	public Print()
	{
		this(1, System.out);
	}

	/**
	 * Creates a new print processor.
	 * 
	 * @param in_arity
	 *          The input arity
	 * @param out
	 *          The print stream to use
	 */
	public Print(int in_arity, PrintStream out)
	{
		super(in_arity);
		m_out = out;
		m_firstOut = true;
	}

	/**
	 * Creates a new print processor with input arity 1
	 * 
	 * @param out
	 *          The print stream to use
	 */
	public Print(PrintStream out)
	{
		this(1, out);
	}
	
	@Override
	public void reset()
	{
		super.reset();
		m_firstOut = true;
	}

	/**
	 * Sets a prefix to display before each event
	 * 
	 * @param prefix
	 *          The prefix; can be any string and include ANSI escape sequences
	 * @return This print processor
	 */
	public /*@ non_null @*/ Print setPrefix(/*@ non_null @*/ String prefix)
	{
		m_prefix = prefix;
		return this;
	}

	/**
	 * Sets a suffix to display before each event. This is not the same thing as the
	 * separator that can be set with {@link #setSeparator(String) setSeparator()}.
	 * The suffix is appended immediately after each event, while the separator is
	 * appended only after the next event arrives.
	 * 
	 * @param suffix
	 *          The suffix; can be any string and include ANSI escape sequences
	 * @return This print processor
	 */
	public /*@ non_null @*/ Print setSuffix(/*@ non_null @*/ String suffix)
	{
		m_suffix = suffix;
		return this;
	}

	/**
	 * Sets a separator to display after each event. This is not the same thing as
	 * the separator that can be set with {@link #setSeparator(String)
	 * setSeparator()}
	 * 
	 * @param separator
	 *          The separator; can be any string and include ANSI escape sequences
	 * @return This print processor
	 */
	public /*@ non_null @*/ Print setSeparator(/*@ non_null @*/ String separator)
	{
		m_separator = separator;
		return this;
	}

	/**
	 * Gets a reference to the print stream to which the character strings will be
	 * sent.
	 * 
	 * @return The print stream
	 */
	public /*@ non_null @*/ PrintStream getPrintStream()
	{
		return m_out;
	}

	/**
	 * Sets the print stream to which the character string will be sent.
	 * 
	 * @param printer
	 *          The print stream
	 * @return This Print processor
	 */
	public Print setPrintStream(/*@ non_null @*/ PrintStream printer)
	{
		m_out = printer;
		return this;
	}

	@Override
	@SuppressWarnings("squid:S1168")
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs)
	{
		if (!m_firstOut)
		{
			beforeSeparator(m_out);
			m_out.print(m_separator);
			afterSeparator(m_out);
		}
		else
		{
			m_firstOut = false;
		}
		beforeEvent(m_out);
		m_out.print(m_prefix);
		if (inputs[0] instanceof byte[])
		{
		  m_out.print(new String((byte[]) inputs[0]));
		}
		else
		{
		  prettyPrint(m_out, inputs[0]);
		}
		m_out.print(m_suffix);
		afterEvent(m_out);
		return true;
	}

	/**
	 * Method that is called before an event is to be printed. Descendants of this
	 * call can be used to make special calls to the underlying print stream, for
	 * example to change its display colors.
	 * 
	 * @param ps
	 *          The print stream
	 */
	protected void beforeEvent(PrintStream ps)
	{
		// Do nothing
	}

	/**
	 * Method that is called after an event is be printed. Descendants of this call
	 * can be used to make special calls to the underlying print stream, for example
	 * to change its display colors.
	 * 
	 * @param ps
	 *          The print stream
	 */
	protected void afterEvent(PrintStream ps)
	{
		// Do nothing
	}

	/**
	 * Method that is called before an separator is to be printed. Descendants of
	 * this call can be used to make special calls to the underlying print stream,
	 * for example to change its display colors.
	 * 
	 * @param ps
	 *          The print stream
	 */
	protected void beforeSeparator(PrintStream ps)
	{
		// Do nothing
	}

	/**
	 * Method that is called after a separator is be printed. Descendants of this
	 * call can be used to make special calls to the underlying print stream, for
	 * example to change its display colors.
	 * 
	 * @param ps
	 *          The print stream
	 */
	protected void afterSeparator(PrintStream ps)
	{
		// Do nothing
	}

	/**
	 * Prints an object in an eye-pleasing way. So far, this method only does
	 * something special for numbers.
	 * 
	 * @param ps The print stream to print into
	 * @param o The object to print
	 */
	protected void prettyPrint(/*@ non_null @*/ PrintStream ps, /*@ non_null @*/ Object o)
	{
		if (o instanceof Number)
		{
			prettyPrint((Number) o);
		}
		else if (o != null && o.getClass().isArray())
		{
			prettyPrint((Object[]) o);
		}
		else
		{
			ps.print(o);
		}
	}

	/**
	 * Prints a number in an eye-pleasing way. In this case, the printer trims the
	 * decimals from a number if it is an integer
	 * 
	 * @param n
	 *          The number
	 */
	protected void prettyPrint(/*@ non_null @*/ Number n)
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

	/**
	 * Prints an array in an eye-pleasing way. In this case, the printer
	 * pretty-prints each element of the array.
	 * 
	 * @param array
	 *          The array
	 */
	protected void prettyPrint(/*@ non_null @*/ Object[] array)
	{
		m_out.print("[");
		for (int i = 0; i < array.length; i++)
		{
			if (i > 0)
			{
				m_out.print(",");
			}
			prettyPrint(m_out, array[i]);
		}
		m_out.print("]");
	}
	
	@Override
	public void stop()
	{
		m_out.close();
	}

	/**
	 * Closes the underlying PrintStream.
	 */
	public void close()
	{
		m_out.close();
	}

	@Override
	public /*@ non_null @*/ Print duplicate(boolean with_state)
	{
		Print print = new Print(getInputArity(), m_out);
		copyInto(print, with_state);
		return print;
	}
	
	/**
	 * Copies the member fields of the current processor into that of another
	 * {@link Print} processor.
	 * @param print The other print processor
	 * @param with_state {@code true} to make a stateful copy, {@link false}
	 * otherwise
	 */
	protected void copyInto(Print print, boolean with_state)
	{
		print.m_prefix = m_prefix;
		print.m_suffix = m_suffix;
		print.m_separator = m_separator;
		if (with_state)
		{
			print.m_firstOut = m_firstOut;
		}
	}
	
	/**
	 * A special type of {@link Print} processor that prints a carriage return by
	 * default between tokens.
	 * @since 0.11
	 */
	public static class Println extends Print
	{
		/**
		 * Creates a new print processor.
		 * @param out The print stream to print into
		 */
		public Println(PrintStream out)
		{
			super(out);
			setSeparator("");
		}
				
		/**
		 * Creates a new print processor that prints to the standard output.
		 */
		public Println()
		{
			this(System.out);
		}
		
		@Override
		protected void afterEvent(PrintStream out)
		{
			out.println();
		}

		
		@Override
		public Println duplicate(boolean with_state)
		{
			Println p = new Println(m_out);
			copyInto(p, with_state);
			return p;
		}
	}
}
