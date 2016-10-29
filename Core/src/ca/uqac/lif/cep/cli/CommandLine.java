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
package ca.uqac.lif.cep.cli;

import java.io.IOException;
import java.util.Scanner;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.interpreter.UserDefinition;
import ca.uqac.lif.cep.tmf.Sink;
import ca.uqac.lif.cep.util.AnsiPrinter;
import ca.uqac.lif.cep.util.AnsiPrinter.Color;

/**
 * A crude command-line interactive interpreter for ESQL.
 *  
 * @author Sylvain Hallé
 */
public class CommandLine
{
	/**
	 * The symbol for the command prompt
	 */
	protected static String s_prompt = "? ";
	
	/**
	 * End greedings ;-)
	 */
	protected static String s_endGreeting = "Tata Edgar";

	public static void main(String[] args) throws IOException
	{
		AnsiPrinter stdout = new AnsiPrinter(System.out);
		Scanner scanner = new Scanner(System.in);
		//	stdout.disableColors();
		Interpreter interpreter = new Interpreter();
		// Load the CLI extension for the interpreter
		interpreter.load(CliGrammar.class);
		boolean exit = false;
		stdout.setForegroundColor(Color.LIGHT_GRAY);
		stdout.println("BeepBeep 3 - A versatile event stream processor");
		stdout.println("(C) 2008-2016 Sylvain Hallé et al., Université du Québec à Chicoutimi");
		stdout.println("This program comes with ABSOLUTELY NO WARRANTY.");
		stdout.println("This is a free software, and you are welcome to redistribute it");
		stdout.println("under certain conditions. See the file LICENSE for details.\n");
		Processor last_processor = null;
		while (!exit)
		{
			stdout.setForegroundColor(Color.PURPLE);
			stdout.print("\n" + s_prompt);
			stdout.resetColors();
			String command = scanner.nextLine();
			// Parse instruction
			command = command.trim();
			if (command.isEmpty())
			{
				continue;
			}
			else if (command.compareToIgnoreCase("QUIT") == 0)
			{
				// Quit
				exit = true;
				continue;
			}
			else if (command.startsWith(",") && last_processor != null)
			{
				// One more event
				if (last_processor instanceof Sink)
				{
					Sink sink = (Sink) last_processor;
					for (int i = 0; i < command.length(); i++)
					{
						sink.pullHard();
					}
				}
			}
			else
			{
				try
				{
					Object o = interpreter.parseQuery(command);
					if (o instanceof Processor)
					{
						last_processor = (Processor) o;
						if (last_processor instanceof Sink)
						{
							Sink sink = (Sink) last_processor;
							for (int loops = 0; loops < 10; loops++)
							{
								sink.pullHard();
							}
						}
					}
					else if (o instanceof UserDefinition)
					{
						UserDefinition def = (UserDefinition) o;
						def.addToInterpreter(interpreter);
					}
				}
				catch (ParseException e)
				{
					stdout.setForegroundColor(Color.RED);
					stdout.print("! ");
					stdout.setForegroundColor(Color.LIGHT_RED);
					stdout.print("Syntax error");
					//e.printStackTrace();
				}
			}
		}
		stdout.println(s_endGreeting);
		scanner.close();
		stdout.close();
	}
}
