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

import java.sql.Connection;
import java.sql.Driver;
import java.sql.DriverManager;
import java.sql.DriverPropertyInfo;
import java.sql.SQLException;
import java.sql.SQLFeatureNotSupportedException;
import java.util.Properties;
import java.util.logging.Logger;

public class BeepBeepDriver implements Driver
{
	public static final String s_prefix = "jdbc:beepbeep:";

  static 
  {
      try 
      {
          DriverManager.registerDriver(new BeepBeepDriver());
      }
      catch (SQLException e) 
      {
          e.printStackTrace();
      }
  }

  /**
   * @see java.sql.Driver#getMajorVersion()
   */
  @Override
  public int getMajorVersion() 
  {
      return 0;
  }

  /**
   * @see java.sql.Driver#getMinorVersion()
   */
  @Override
  public int getMinorVersion() 
  {
      return 0;
  }

  /**
   * @see java.sql.Driver#jdbcCompliant()
   */
  @Override
  public boolean jdbcCompliant() 
  {
      return false;
  }

  /**
   * @see java.sql.Driver#acceptsURL(java.lang.String)
   */
  @Override
  public boolean acceptsURL(String url) 
  {
      return isValidURL(url);
  }

  /**
   * Validates a URL
   * @param url The URL. It is considered valid if it begins by the string
   *  <code>jdbc:beepbeep:</code>
   * @return <code>true</code> if the URL is valid, <code>false</code> otherwise
   */
  public static boolean isValidURL(String url) 
  {
      return url != null && url.toLowerCase().startsWith(s_prefix);
  }

  /**
   * @see java.sql.Driver#getPropertyInfo(java.lang.String, java.util.Properties)
   */
  @Override
  public DriverPropertyInfo[] getPropertyInfo(String url, Properties info) throws SQLException 
  {
      return new DriverPropertyInfo[0];
  }

  /**
   * @see java.sql.Driver#connect(java.lang.String, java.util.Properties)
   */
  @Override
  public Connection connect(String url, Properties info) throws SQLException 
  {
      return createConnection(url, info);
  }

  /**
   * Gets the location to the database from a given URL.
   * @param url The URL to extract the location from.
   * @return The location to the database.
   */
  static String extractAddress(String url) 
  {
      // if no file name is given use a memory database
      return s_prefix.equalsIgnoreCase(url) ? ":memory:" : url.substring(s_prefix.length());
  }

  /**
   * Creates a new database connection to a given URL.
   * @param url The connection URL
   * @param prop The properties
   * @return A <code>Connection</code> object that represents a connection
   *  to the URL
   * @throws SQLException If the URL provided is invalid
   * @see java.sql.Driver#connect(java.lang.String, java.util.Properties)
   */
  public static Connection createConnection(String url, Properties prop) throws SQLException 
  {
      if (!isValidURL(url))
      {
          throw new SQLException("invalid database address: " + url);
      }

      url = url.trim();
      return new BeepBeepConnection(url, extractAddress(url), prop);
  }

  	// @Override -- Comment out annotation for Java 1.6 compliance
	public Logger getParentLogger() throws SQLFeatureNotSupportedException
	{
		// TODO Auto-generated method stub
		return null;
	}
}
