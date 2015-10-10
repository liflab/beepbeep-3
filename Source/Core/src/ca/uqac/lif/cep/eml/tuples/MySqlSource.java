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
package ca.uqac.lif.cep.eml.tuples;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.ResultSetMetaData;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.List;
import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

import ca.uqac.lif.cep.Source;

/**
 * Converts a query to a MySQL database into a trace of named tuples. 
 */
public class MySqlSource extends Source 
{
	protected final String m_tableName;

	protected final String m_databaseName;

	protected static final String s_jdbcDriver = "com.mysql.jdbc.Driver";  

	/**
	 * The username used to connect to the database
	 */
	protected final String m_username;
	
	/**
	 * The password used to connect to the database
	 */
	protected final String m_password;
	
	protected Connection conn = null;
	protected Statement stmt = null;
	protected ResultSet rs = null; 

	/**
	 * Whether the tuples of the underlying relation should be output
	 * one by one on every call to {@link #compute(Vector)}, or
	 * output all at once on the first call to that method.
	 */
	protected boolean m_feedOneByOne;

	/**
	 * Builds a MySQL source.
	 * @param username The username used to connect to the database
	 * @param password The password used to connect to the database
	 * @param dbname The database name to be read from
	 * @param tablename The name of the table to be read from. Actually, this does not need
	 * to be a table name, as any SQL expression that returns a table (e.g.
	 * a <code>SELECT</code> statement) can do.
	 */
	public MySqlSource(String username, String password, String dbname, String tablename)
	{
		super(1);
		m_username = username;
		m_password = password;
		m_tableName = tablename;
		m_databaseName = dbname;
		m_feedOneByOne = true;
	}

	/**
	 * Sets whether the tuples of the underlying relation should be output
	 * one by one on every call to {@link #compute(Vector)}, or
	 * output all at once on the first call to that method. While this
	 * has no effect on the end result, it might have an impact on the
	 * performance (e.g. if the source outputs a very large number of
	 * tuples in the output queue, which must be stored in memory).
	 * @param b Set to <code>true</code> to feed the tuples one by one,
	 *   false otherwise
	 */
	public void setFeedOneByOne(boolean b)
	{
		m_feedOneByOne = b;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		if (conn == null)
		{
			// First connect to the database
			String db_url = "jdbc:mysql://localhost/" + m_databaseName;
			try 
			{
				conn = DriverManager.getConnection(db_url, m_username, m_password);
				stmt = conn.createStatement();
			    rs = stmt.executeQuery(m_tableName);
			} 
			catch (SQLException e) 
			{
				e.printStackTrace();
			}
		}
		try 
		{
			ResultSetMetaData metadata = rs.getMetaData();
			List<String> col_names = new ArrayList<String>();
			int col_count = metadata.getColumnCount();
			for (int i = 0; i < col_count; i++)
			{
				col_names.add(metadata.getColumnName(i));
			}
			while (rs.next())
			{
				NamedTupleMap nt = new NamedTupleMap();
				for (int i = 1; i <= col_count; i++)
				{
					String name = col_names.get(i);
					Object value = rs.getObject(i);
					if (value instanceof String)
					{
						nt.put(name, new EmlString((String) value));
					}
					else if (value instanceof Number)
					{
						nt.put(name,  EmlNumber.toEmlNumber(value));
					}
				}
			}
		} 
		catch (SQLException e) 
		{
			e.printStackTrace();
		}
		return null;
	}

	public static void build(Stack<Object> stack) 
	{
		String password = (String) stack.pop();
		stack.pop(); // PASSWORD
		stack.pop(); // ,
		String username = (String) stack.pop();
		stack.pop(); // USER
		stack.pop(); // ,
		String databaseName = (String) stack.pop();
		stack.pop(); // DATABASE
		stack.pop(); // IN
		String tableName = (String) stack.pop();
		stack.pop(); // TABLE
		MySqlSource source = new MySqlSource(username, password, databaseName, tableName);
		stack.push(source);
	}
}
