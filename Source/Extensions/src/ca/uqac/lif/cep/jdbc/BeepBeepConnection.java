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
package ca.uqac.lif.cep.jdbc;

import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.util.Properties;

import ca.uqac.lif.cep.interpreter.Interpreter;

public class BeepBeepConnection extends EmptyConnection
{
	protected Interpreter m_interpreter;
	
	BeepBeepConnection(String url, String fileName, Properties prop)
	{
		super();
		m_interpreter = new Interpreter();
	}
	
	@Override
	public BeepBeepStatement createStatement()
	{
		return new BeepBeepStatement(m_interpreter);
	}
	
	@Override
	public void close()
	{
		m_interpreter.reset();
	}

	@Override
	public PreparedStatement prepareStatement(String query) throws SQLException
	{
		return new BeepBeepPreparedStatement(m_interpreter, query);
	}

}
