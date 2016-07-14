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

import java.sql.Array;
import java.sql.Blob;
import java.sql.CallableStatement;
import java.sql.Clob;
import java.sql.DatabaseMetaData;
import java.sql.NClob;
import java.sql.PreparedStatement;
import java.sql.SQLClientInfoException;
import java.sql.SQLException;
import java.sql.SQLWarning;
import java.sql.SQLXML;
import java.sql.Savepoint;
import java.sql.Statement;
import java.sql.Struct;
import java.util.Map;
import java.util.Properties;
import java.util.concurrent.Executor;

/**
 * An empty implementation of the JDBC Connection class. 
 * @author Sylvain Hallé
 */
abstract class EmptyConnection implements java.sql.Connection
{
		EmptyConnection()
		{
			super();
		}
		
		public void close()
		{
			// TODO Auto-generated method stub			
		}

		@Override
		public boolean isWrapperFor(Class<?> arg0) throws SQLException
		{
			// TODO Auto-generated method stub
			return false;
		}

		@Override
		public <T> T unwrap(Class<T> iface) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		// @Override -- Comment out annotation for Java 1.6 compliance
		public void abort(Executor executor) throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void clearWarnings() throws SQLException
		{
			// Do nothing
		}

		@Override
		public void commit() throws SQLException
		{
			// Do nothing
			
		}

		@Override
		public Array createArrayOf(String arg0, Object[] arg1) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Blob createBlob() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Clob createClob() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public NClob createNClob() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public SQLXML createSQLXML() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Statement createStatement() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Statement createStatement(int arg0, int arg1) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Statement createStatement(int arg0, int arg1, int arg2)
				throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Struct createStruct(String arg0, Object[] arg1) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public boolean getAutoCommit() throws SQLException
		{
			// TODO Auto-generated method stub
			return false;
		}

		@Override
		public String getCatalog() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Properties getClientInfo() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public String getClientInfo(String arg0) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public int getHoldability() throws SQLException
		{
			// TODO Auto-generated method stub
			return 0;
		}

		@Override
		public DatabaseMetaData getMetaData() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		// @Override -- Comment out annotation for Java 1.6 compliance
		public int getNetworkTimeout() throws SQLException
		{
			// TODO Auto-generated method stub
			return 0;
		}

		// @Override -- Comment out annotation for Java 1.6 compliance
		public String getSchema() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public int getTransactionIsolation() throws SQLException
		{
			// TODO Auto-generated method stub
			return 0;
		}

		@Override
		public Map<String, Class<?>> getTypeMap() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public SQLWarning getWarnings() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public boolean isClosed() throws SQLException
		{
			// TODO Auto-generated method stub
			return false;
		}

		@Override
		public boolean isReadOnly() throws SQLException
		{
			// TODO Auto-generated method stub
			return false;
		}

		@Override
		public boolean isValid(int timeout) throws SQLException
		{
			// TODO Auto-generated method stub
			return false;
		}

		@Override
		public String nativeSQL(String sql) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public CallableStatement prepareCall(String sql) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public CallableStatement prepareCall(String sql, int resultSetType,
				int resultSetConcurrency) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public CallableStatement prepareCall(String sql, int resultSetType,
				int resultSetConcurrency, int resultSetHoldability) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public abstract PreparedStatement prepareStatement(String sql) throws SQLException;

		@Override
		public PreparedStatement prepareStatement(String sql, int autoGeneratedKeys)
				throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public PreparedStatement prepareStatement(String sql, int[] columnIndexes)
				throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public PreparedStatement prepareStatement(String sql, String[] columnNames)
				throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public PreparedStatement prepareStatement(String sql, int resultSetType,
				int resultSetConcurrency) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public PreparedStatement prepareStatement(String sql, int resultSetType,
				int resultSetConcurrency, int resultSetHoldability) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public void releaseSavepoint(Savepoint savepoint) throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void rollback() throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void rollback(Savepoint savepoint) throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void setAutoCommit(boolean autoCommit) throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void setCatalog(String catalog) throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void setClientInfo(Properties properties)
				throws SQLClientInfoException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void setClientInfo(String name, String value)
				throws SQLClientInfoException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void setHoldability(int holdability) throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		// @Override -- Comment out annotation for Java 1.6 compliance
		public void setNetworkTimeout(Executor executor, int milliseconds)
				throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void setReadOnly(boolean readOnly) throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public Savepoint setSavepoint() throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Savepoint setSavepoint(String name) throws SQLException
		{
			// TODO Auto-generated method stub
			return null;
		}

		// @Override -- Comment out annotation for Java 1.6 compliance
		public void setSchema(String schema) throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void setTransactionIsolation(int level) throws SQLException
		{
			// TODO Auto-generated method stub
			
		}

		@Override
		public void setTypeMap(Map<String, Class<?>> map) throws SQLException
		{
			// TODO Auto-generated method stub
			
		}
}
