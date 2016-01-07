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
package ca.uqac.lif.cep.interpreter;

import org.junit.Test;

/**
 * A front-end to the {@link Interpreter} class that provides extra public 
 * methods that should only be used for testing
 */
public class InterpreterTestFrontEnd extends Interpreter 
{
	public InterpreterTestFrontEnd()
	{
		super();
	}
	
	@Override
	public Object parseLanguage(String property, String start_symbol) throws ParseException
	{
		return super.parseLanguage(property, start_symbol);
	}
	
	public void setDebugMode(boolean b)
	{
		m_parser.setDebugMode(b);
	}
	
	@Test
	public void dummyTest()
	{
		// Do nothing
	}
}
