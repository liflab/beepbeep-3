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

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;

/**
 * Use the <code>COMBINE</code> keyword to apply a cumulative
 * function to a stream of events.
 * 
 * @author Sylvain Hallé
 */
public class Combine
{
	public static void main(String[] args) throws ParseException
	{
		// SNIP
		Interpreter my_int = Interpreter.newInterpreter();
		Pullable p = my_int.executeQuery("COMBINE CONSTANT 2 WITH ADDITION");
		for (int i = 0; i < 5; i++ )
		{
			Object o = p.pull();
			System.out.printf("The event is: %s\n", o);
		}
		// SNIP
		System.out.println("-----");
		// Just for fun, let's try the same thing with multiplication
		p = my_int.executeQuery("COMBINE CONSTANT 2 WITH MULTIPLICATION");
		for (int i = 0; i < 5; i++ )
		{
			Object o = p.pull();
			System.out.printf("The event is: %s\n", o);
		}
	}
}
