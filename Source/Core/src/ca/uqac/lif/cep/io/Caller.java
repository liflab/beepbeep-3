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
package ca.uqac.lif.cep.io;

import java.util.Queue;
import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.SingleProcessor;
import ca.uqac.lif.cep.util.CommandRunner;

/**
 * Processor calling an external command upon receiving an event,
 * and returning the output of that command as its output stream.
 * 
 * @author Sylvain Hallé
 *
 */
public class Caller extends SingleProcessor
{
	/**
	 * The command to call
	 */
	protected final String m_command;
	
	public Caller(String command)
	{
		super(1, 1);
		m_command = command;
	}
	
	/**
	 * The time to wait (in milliseconds) before polling the command's result 
	 */
	protected static long s_waitInterval = 100;
	
	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		// Pass the event (as is) to the standard input of the command
		byte[] contents = CommandRunner.runAndGet(m_command, (byte[]) inputs[0]);
		return wrapObject(contents);
	}

	public static void build(Stack<Object> stack) throws ConnectorException
	{
		stack.pop(); // (
		Processor p = (Processor) stack.pop();
		stack.pop(); // )
		stack.pop(); // ON
		String command = (String) stack.pop();
		stack.pop(); // CALL
		Caller c = new Caller(command);
		Connector.connect(p, c);
		stack.push(c);
	}
	
	@Override
	public Caller clone()
	{
		return new Caller(m_command);
	}
}
