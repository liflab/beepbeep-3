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
package ca.uqac.lif.cep.util;

import java.util.logging.Logger;

/**
 * A dummy logger that traps exceptions. This is so that the code
 * complies with the rule that stipulates that 
 * <code>Throwable.printStackTrace(...)</code> should not be called.
 * 
 * @author Sylvain Hallé
 */
public class BeepBeepLogger
{
	/**
	 * A dummy logger instance used by other classes
	 */
	public static final Logger logger = Logger.getLogger(BeepBeepLogger.class.getName());
	
	/**
	 * Utility classes should not have public constructors
	 */
	private BeepBeepLogger()
	{
		throw new IllegalAccessError("Utility class");
	}
}
