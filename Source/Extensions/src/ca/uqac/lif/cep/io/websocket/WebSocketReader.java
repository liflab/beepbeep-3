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
package ca.uqac.lif.cep.io.websocket;

import java.net.URI;
import java.util.Queue;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.Pushable;
import ca.uqac.lif.cep.SingleProcessor;

import org.java_websocket.client.WebSocketClient;
import org.java_websocket.handshake.ServerHandshake;

/**
 * Reads chunks of data from a websocket.
 * These chunks are returned as events in the form of strings.
 * This processor <strong>pushes</strong> events downstream.
 * You will not get anything if you use its output pullables.
 * 
 * @author Sylvain Hallé
 */ 
public class WebSocketReader extends SingleProcessor
{
	/**
	 * The URI of the web socket server
	 */
	private URI m_serverUri;
	
	WebSocketReader()
	{
		super(0, 1);
	}
	
	/**
	 * Creates a new web socket reader
	 * @param server_uri The URI of the server this reader should connect to
	 */
	public WebSocketReader(URI server_uri)
	{
		this();
		m_serverUri = server_uri;
	}

	@Override
	protected Queue<Object[]> compute(Object[] inputs)
	{
		return null;
	}

	@Override
	public Processor clone() 
	{
		return new WebSocketReader(m_serverUri);
	}
	
	/**
	 * Gets an instance of web socket client associated to this
	 * processor
	 * @return The web socket client
	 */
	public WebSocketClient getWebSocketClient()
	{
		return new WebSocketClientWrapper(m_serverUri);
	}
	
	/**
	 * A wrapper class so that this processor can be used as an instance
	 * of <code>WebSocketClient</code>
	 */
	protected class WebSocketClientWrapper extends WebSocketClient
	{
		public WebSocketClientWrapper(URI serverURI)
		{
			super(serverURI);
		}

		@Override
		public void onClose(int arg0, String arg1, boolean arg2) 
		{
			// Do nothing
		}

		@Override
		public void onError(Exception arg0) 
		{
			// Do nothing
		}

		@Override
		public synchronized void onMessage(String arg0) 
		{
			Pushable pushable = getPushableOutput(0);
			pushable.push(arg0);
		}

		@Override
		public void onOpen(ServerHandshake arg0) 
		{
			// Do nothing
		}
	}
}
