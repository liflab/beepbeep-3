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
 * Create a constant stream of events with the
 * <code>CONSTANT</code> keyword.
 * 
 * @author Sylvain Hallé
 */
public class ConstantProcessor
{
	public static void main(String[] args) throws ParseException
	{
		// SNIP
		Interpreter my_int = Interpreter.newInterpreter();
		Pullable p = my_int.executeQuery("CONSTANT 1");
		for (int i = 0; i < 10; i++ )
		{
			Object o = p.pull();
			System.out.printf("The event is: %s\n", o);
		}
		// SNIP
	}
}
