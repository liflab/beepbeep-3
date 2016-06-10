/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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
package ca.uqac.lif.cep.examples.simple;

import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.tuples.EmlNumber;
import ca.uqac.lif.cep.tuples.TupleGrammar;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.io.StreamGrammar;
import ca.uqac.lif.cep.ltl.LtlGrammar;

/**
 * Simple example of the usage of Linear Temporal Logic.
 * <p>
 * In this example, we read tuples from a CSV file structured as follows:
 * <pre>
 * a,b,c
 * 0,1,2
 * 1,0,1
 * ...
 * </pre>
 * Each line of the file defines the values of attributes <i>a</i>, <i>b</i> 
 * and <i>c</i> of a new tuple. We are interested in computing the number of
 * times that a tuple where <i>a</i>&nbsp;&lt;&nbsp;2</i> is followed by a tuple where
 * <i>b</i>&nbsp;&gt;&nbsp;1</i>. If <code>@P</code> is the trace to read
 * from, the first condition can be written as:
 * <pre>
 * SELECT (a) LESS THAN (2) FROM (@P)
 * </pre>
 * and the second as:
 * <pre>
 * SELECT (b) GREATER THAN (1) FROM (@P)
 * </pre>
 * The output of both expressions is a trace of Boolean values, one for each
 * input event.
 * <p>
 * The pattern we are looking for can be easily expressed with temporal logic,
 * by writing
 * <pre>
 * (SELECT (a) LESS THAN (2) FROM (@P)) AND (NEXT (SELECT (b) GREATER THAN (1) FROM (@P)))
 * </pre>
 * The output of this expression is a trace of Boolean values; its <i>i</i>-th
 * event is the value "true" if, in the input trace <code>@P</code>,
 * <i>a</i>&nbsp;&lt;&nbsp;2</i> in the <i>i</i>-th event, and
 * <i>b</i>&nbsp;&gt;&nbsp;1</i> in the (<i>i</i>+1)-th event. Notice how the
 * expression needs to see what is in event <i>i</i>+1 before emitting a value
 * for event <i>i</i>.
 * <p>
 * Finally, we must count the number of times this trace contains the Boolean
 * value true. We can define the count of a trace as the expression:
 * <pre>
 * WHEN @P IS A processor: THE COUNT OF ( @P ) IS THE processor COMBINE (SELECT 1 FROM (@P)) WITH SUM
 * </pre>
 * and then use it to count how many events are the value true with:
 * <pre>
 * THE COUNT OF ((...) WHERE (x) = (true))
 * </pre> 
 * where <code>...</code> should be replaced by the pattern we have 
 * written previously.
 * <p>
 * The end result is a trace of numbers; a new number (incrementing the 
 * previous number by one) is output every time an event where
 * <i>a</i>&nbsp;&lt;&nbsp;2</i> is read, followed by an event where
 * <i>b</i>&nbsp;&gt;&nbsp;1</i>.
 */
public class TemporalLogic 
{
	public static void main(String[] args)
	{
		// Instantiate an empty interpreter
		Interpreter my_int = new Interpreter();
		// Import grammar extensions for I/O
		my_int.extendGrammar(StreamGrammar.class);
		// Import grammar extensions for tuples
		my_int.extendGrammar(TupleGrammar.class);
		// Import grammar extensions for LTL
		my_int.extendGrammar(LtlGrammar.class);
		
		// Add a few definitions
		my_int.executeQuery("WHEN @P IS A processor: THE COUNT OF ( @P ) IS THE processor COMBINE (SELECT 1 FROM (@P)) WITH SUM");
		my_int.executeQuery("WHEN @P IS A processor: MY PATTERN IN ( @P ) IS THE processor (SELECT (a) LESS THAN (2) FROM (@P)) AND (X (SELECT (a) GREATER THAN (1) FROM (@P)))");
		
		// Read tuples from a file
		Pullable result = my_int.executeQuery("THE COUNT OF ((MY PATTERN IN (THE TUPLES OF FILE \"tuples1.csv\")) WHERE (x) = (true))");
		while (result.hasNextHard() != Pullable.NextStatus.NO)
		{
			//EmlBoolean n = (EmlBoolean) result.pullHard();
			EmlNumber n = (EmlNumber) result.pullHard();
			System.out.println(n);			
		}
	}
}
