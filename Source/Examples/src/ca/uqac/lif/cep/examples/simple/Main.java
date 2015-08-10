/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package ca.uqac.lif.cep.examples.simple;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.eml.tuples.*;
import ca.uqac.lif.cep.interpreter.*;
import ca.uqac.lif.cep.io.StreamGrammar;

public class Main 
{

	public static void main(String[] args) 
	{
		// Instantiate an empty interpreter
		Interpreter my_int = new Interpreter();
		// Import grammar extensions for I/O
		my_int.extendGrammar(StreamGrammar.class);
		// Import grammar extensions for tuples
		my_int.extendGrammar(TupleGrammar.class);
		
		// Add a few definitions
		my_int.executeQuery("WHEN @P IS A processor: THE COUNT OF ( @P ) IS THE processor COMBINE (SELECT 1 FROM (@P)) WITH SUM");
		my_int.executeQuery("WHEN @P IS A processor: THE SUM OF ( @P ) IS THE processor COMBINE (@P) WITH SUM");
		my_int.executeQuery("WHEN @P IS A processor: THE AVERAGE OF ( @P ) IS THE processor SELECT (T.x) ÷ (U.x) FROM (THE SUM OF (@P) AS T, THE COUNT OF (@P) AS U)");
		
		// Create a trace
		my_int.executeQuery("MY TRACE IS THE processor SELECT SIN(x) FROM (THE COUNT OF (1))");
		
		// Do something with this trace
		Pullable result = my_int.executeQuery("THE AVERAGE OF (MY TRACE)");
		for (int i = 0; i < 10; i++)
		{
			EmlNumber t = (EmlNumber) result.pull();
			System.out.println(t);
		}
	}

}
