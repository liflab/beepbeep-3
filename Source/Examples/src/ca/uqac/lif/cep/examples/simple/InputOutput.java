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
import ca.uqac.lif.cep.eml.tuples.NamedTuple;
import ca.uqac.lif.cep.eml.tuples.TupleGrammar;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.io.StreamGrammar;

public class InputOutput 
{
	public static void main(String[] args)
	{
		// Instantiate an empty interpreter
		Interpreter my_int = new Interpreter();
		// Import grammar extensions for I/O
		my_int.extendGrammar(StreamGrammar.class);
		// Import grammar extensions for tuples
		my_int.extendGrammar(TupleGrammar.class);
		
		// Read tuples from a file
		Pullable result = my_int.executeQuery("SELECT a AS k FROM THE TUPLES OF FILE \"tuples.csv\"");
		while (result.hasNextHard() != Pullable.NextStatus.NO)
		{
			NamedTuple t = (NamedTuple) result.pull();
			System.out.println(t.get("k"));			
		}
	}
}
