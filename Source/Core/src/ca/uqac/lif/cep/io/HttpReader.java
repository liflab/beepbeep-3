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
package ca.uqac.lif.cep.io;

import java.io.IOException;
import java.io.InputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.util.Queue;
import java.util.Stack;
import java.util.Vector;

/**
 * Reads chunks of data from an URL, using an HTTP request.
 * These chunks are returned as events in the form of strings.
 * @author sylvain
 */
public class HttpReader extends StreamReader
{
	/**
	 * The User-Agent string that the reader will send in its HTTP
	 * requests
	 */
	public static final String s_userAgent = "BeepBeep3";
	
	/**
	 * The URL to read from
	 */
	protected String m_url;
	
	public HttpReader()
	{
		super();
		m_url = "";
	}
	
	/**
	 * Instantiates an HTTP reader with an URL. Note that no request is
	 * sent over the network until the first call to {@link #compute(Vector)}.
	 * @param url The URL
	 */
	public HttpReader(String url)
	{
		super();
		m_url = url;
	}
	
	/**
	 * Sets the URL to read from
	 * @param url The URL
	 */
	public void setUrl(String url)
	{
		m_url = url;
	}

	@Override
	protected Queue<Vector<Object>> compute(Vector<Object> inputs)
	{
		if (m_fis == null)
		{
			// No input stream; send HTTP request to get it
			InputStream is = sendGet(m_url);
			setInputStream(is);
		}
		return super.compute(inputs);
	}

	@Override
	public void build(Stack<Object> stack)
	{
		m_url = (String) stack.pop();
		stack.pop(); // URL
		stack.push(this);
	}
	
	/**
	 * Sends a GET request to the specified URL, and obtains
	 * an input stream with the contents of the response
	 * @param url The URL to send the HTTP request
	 * @return An input stream, where the HTTP response can be
	 *   read from
	 */
	protected static InputStream sendGet(String url)
	{
		InputStream is = null;
		try
		{
			URL obj = new URL(url);
			HttpURLConnection con = (HttpURLConnection) obj.openConnection();
			con.setRequestMethod("GET");
			con.setRequestProperty("User-Agent", s_userAgent);
			con.getResponseCode();
			is = con.getInputStream();
		} 
		catch (IOException e)
		{
			e.printStackTrace();
		}
		return is;
	}

}
