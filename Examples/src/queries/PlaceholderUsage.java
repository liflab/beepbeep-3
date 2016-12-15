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
package queries;

import java.io.InputStream;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;

/**
 * Use a placeholder to refer to an external source of events.
 * 
 * @author Sylvain Hallé
 */
public class PlaceholderUsage
{
	public static void main(String[] args) throws ParseException
	{
		// SNIP
		Interpreter my_int = Interpreter.newInterpreter();
		// Get a hold of an input stream to a text file
		InputStream is = PlaceholderUsage.class.getResourceAsStream("numbers1.txt");
		// Tell the interpreter to create a LineReader out of this input
		// stream, which we will refer to in queries as the placeholder
		// "@numbers"
		my_int.addLineReader("@numbers", is);
		// Execute a query. In this case, the query is just the processor
		// itself, so it will output each line of the input file one by one
		Pullable p = my_int.executeQuery("@numbers");
		for (Object o : p)
		{
			System.out.printf("The event is: %s\n", o);
		}
		// SNIP
	}
}
