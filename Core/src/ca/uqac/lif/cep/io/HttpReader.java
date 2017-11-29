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

import java.io.IOException;
import java.io.InputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.util.Queue;

import ca.uqac.lif.cep.ProcessorException;

/**
 * Reads chunks of data from an URL, using an HTTP request.
 * These chunks are returned as events in the form of strings.
 * 
 * @author Sylvain Hallé
 */
@SuppressWarnings("squid:S2160")
public class HttpReader extends StreamReader
{
	/**
	 * 
	 */
	private static final long serialVersionUID = -4529083150218166174L;

	/**
	 * The User-Agent string that the reader will send in its HTTP
	 * requests
	 */
	public static final String s_userAgent = "BeepBeep3";

	/**
	 * The URL to read from
	 */
	protected final String m_url;

	/**
	 * Instantiates an HTTP reader with an URL. Note that no request is
	 * sent over the network until the first call to {@link #compute(Object[], Queue)}.
	 * @param url The URL to read from
	 */
	public HttpReader(String url)
	{
		super();
		m_url = url;
	}

	@Override
	protected boolean compute(Object[] inputs, Queue<Object[]> outputs) throws ProcessorException
	{
		if (m_fis == null)
		{
			// No input stream; send HTTP request to get it
			try
			{
				InputStream is = sendGet(m_url);
				setInputStream(is);
			}
			catch (IOException e)
			{
				throw new ProcessorException(e);
			}
			
		}
		return super.compute(inputs, outputs);
	}

	/**
	 * Sends a GET request to the specified URL, and obtains
	 * an input stream with the contents of the response
	 * @param url The URL to send the HTTP request
	 * @return An input stream, where the HTTP response can be
	 *   read from
	 */
	protected static InputStream sendGet(String url) throws IOException
	{
		InputStream is = null;
		URL obj = new URL(url);
		HttpURLConnection con = (HttpURLConnection) obj.openConnection();
		con.setRequestMethod("GET");
		con.setRequestProperty("User-Agent", s_userAgent);
		con.getResponseCode();
		is = con.getInputStream();
		return is;
	}

}
