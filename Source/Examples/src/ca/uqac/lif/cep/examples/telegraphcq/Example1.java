/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hall�

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
package ca.uqac.lif.cep.examples.telegraphcq;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.eml.tuples.Tuple;
import ca.uqac.lif.cep.eml.tuples.TupleGrammar;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.io.StreamGrammar;

public class Example1 
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

		// Name the input trace
		my_int.executeQuery("ClosingStockPrices IS THE processor THE TUPLES OF FILE \"ClosingStockPrices.csv\"");
		
		// Read tuples from a file
		Pullable result = my_int.executeQuery("EVERY 5TH OF (APPLY (THE AVERAGE OF (0)) ON (SELECT closingPrice FROM (((SELECT closingPrice, stockSymbol FROM (ClosingStockPrices)) WHERE (stockSymbol) = (\"MSFT\")))) ON A WINDOW OF 5)");
		while (result.hasNextHard() != Pullable.NextStatus.NO)
		{
			Tuple t = (Tuple) result.pull();
			System.out.println(t);			
		}
	}
}
