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
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Scanner;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.epl.EplGrammar;
import ca.uqac.lif.cep.epl.Sink;
import ca.uqac.lif.cep.interpreter.Interpreter;
import ca.uqac.lif.cep.interpreter.Interpreter.ParseException;
import ca.uqac.lif.cep.interpreter.UserDefinition;
import ca.uqac.lif.cep.io.StreamGrammar;
import ca.uqac.lif.cep.util.AnsiPrinter;
import ca.uqac.lif.cep.util.AnsiPrinter.Color;

public class CommandLine
{
	protected static String s_prompt = "? ";
	
	protected static String s_endGreeting = "Tata Edgar";

	public static void main(String[] args) throws IOException
	{
		AnsiPrinter stdout = new AnsiPrinter(System.out);
		Scanner scanner = new Scanner(System.in);
		//	stdout.disableColors();
		Interpreter interpreter = new Interpreter();
		// Load extensions for the interpreter
		{
			interpreter.extendGrammar(EplGrammar.class);
			interpreter.extendGrammar(CliGrammar.class);
			//interpreter.extendGrammar(TupleGrammar.class);
			interpreter.extendGrammar(StreamGrammar.class);
		}
		boolean exit = false;
		stdout.setForegroundColor(Color.LIGHT_GRAY);
		stdout.println("BeepBeep 3 - A versatile event stream processor");
		stdout.println("(C) 2008-2015 Sylvain Hallé et al., Université du Québec à Chicoutimi");
		stdout.println("This program comes with ABSOLUTELY NO WARRANTY.");
		stdout.println("This is a free software, and you are welcome to redistribute it");
		stdout.println("under certain conditions. See the file LICENSE for details.\n");
		Processor last_processor = null;
		while (!exit)
		{
			stdout.setForegroundColor(Color.PURPLE);
			stdout.print("\n" + s_prompt);
			stdout.setForegroundColor(Color.BLACK);
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

	protected static class CharScanner
	{
		protected InputStream m_is;

		protected volatile boolean m_exit;

		public CharScanner(InputStream is)
		{
			super();
			m_is = is;
		}

		public char nextChar()
		{
			InputStreamReader reader = new InputStreamReader(m_is);
			m_exit = false;
			while(!m_exit) 
			{ 
				try
				{
					if (reader.ready()) 
					{ 
						// read a character and process it
						return (char) reader.read();
					}
				}
				catch (IOException e)
				{
					// Do nothing
				} 
				// Lets not hog any cpu time 
				try 
				{ 
					Thread.sleep(50); 
				} 
				catch (InterruptedException ex) 
				{ 
					// can't do much about it can we? Ignoring  
				} 
			}
			return (char) 0;
		}
	}
}
