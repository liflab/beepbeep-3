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
 * Use the <code>APPLY</code> keyword to apply a
 * function to a stream of events.
 * 
 * @author Sylvain Hallé
 */
public class UserDefinitionFunction
{
	public static void main(String[] args) throws ParseException
	{
		// SNIP
		Interpreter my_int = Interpreter.newInterpreter();
		my_int.addLineReader("@num1", UserDefinitionFunction.class.getResourceAsStream("numbers1.txt"));
		my_int.addLineReader("@num2", UserDefinitionFunction.class.getResourceAsStream("numbers2.txt"));
		my_int.executeQuery("WHEN @X IS A FUNCTION, @Y IS A FUNCTION: "
				+ "THE MODULUS OF @X AND @Y IS THE FUNCTION "
				+ "√(((@X)^2) + ((@Y)^2))");
		Pullable p = my_int.executeQuery("APPLY THE MODULUS OF $0 AND $1 WITH "
				+ "(APPLY (TURN $0 INTO A NUMBER) WITH @num1) AS $x, "
				+ "(APPLY (TURN $0 INTO A NUMBER) WITH @num2) AS $y");
		for (int i = 0; i < 5; i++ )
		{
			Object o = p.pull();
			System.out.printf("The event is: %s\n", o);
		}
		// SNIP
	}
}
