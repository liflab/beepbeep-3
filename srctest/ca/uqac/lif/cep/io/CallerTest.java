/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2017 Sylvain Hallé

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

import static org.junit.Assert.*;

import org.junit.Assume;
import org.junit.Test;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Pullable;
import ca.uqac.lif.cep.Pullable.PullableException;
import ca.uqac.lif.cep.tmf.QueueSource;

/**
 * Unit tests for the {@link Call} processor. 
 * @author Sylvain Hallé
 *
 */
public class CallerTest 
{
	/**
	 * OS name; necessary for OS-dependent test cases
	 */
	protected static final String s_osName = System.getProperty("os.name");
	
	@Test(expected=PullableException.class)
	public void testCommandNotExists()
	{
		QueueSource source = new QueueSource();
		source.setEvents(new Object[]{new byte[0]});
		Call caller = new Call("foo"); // let's hope this command does not exist!
		Connector.connect(source, caller);
		Pullable p = caller.getPullableOutput();
		p.pull();
	}
	
	@Test
	public void testCommandWindows()
	{
		Assume.assumeTrue(s_osName.contains("Windows"));
		QueueSource source = new QueueSource();
		source.setEvents(new Object[]{new byte[0]});
		// echo is a command that exists in both Windows and Linux
		Call caller = new Call("cmd.exe", "/c", "echo foo");
		Connector.connect(source, caller);
		Pullable p = caller.getPullableOutput();
		byte[] bytes = (byte[]) p.pull();
		assertNotNull(bytes);
		String s = new String(bytes);
		assertEquals("foo", s.trim());
	}
	
	@Test
	public void testCommandLinux()
	{
		Assume.assumeFalse(s_osName.contains("Windows"));
		QueueSource source = new QueueSource();
		source.setEvents(new Object[]{new byte[0]});
		// echo is a command that exists in both Windows and Linux
		Call caller = new Call("echo", "foo");
		Connector.connect(source, caller);
		Pullable p = caller.getPullableOutput();
		byte[] bytes = (byte[]) p.pull();
		assertNotNull(bytes);
		String s = new String(bytes);
		assertEquals("foo", s.trim());
	}
}
