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

import static org.junit.Assert.*;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.UnknownHostException;
import java.util.Collection;
import java.util.Queue;

import org.java_websocket.WebSocket;
import org.java_websocket.client.WebSocketClient;
import org.java_websocket.handshake.ClientHandshake;
import org.java_websocket.server.WebSocketServer;
import org.junit.Test;

import ca.uqac.lif.cep.BeepBeepUnitTest;
import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.epl.QueueSink;
import ca.uqac.lif.cep.io.websocket.WebSocketReader;

/**
 * Unit tests for the WebSocket reader.
 * @author Sylvain Hallé
 */
public class WebSocketTest extends BeepBeepUnitTest
{
	/**
	 * In this test, we insert sleep statements. If the operations are
	 * executed too fast, the client may not connect to the server, or
	 * may not have received yet the message sent by the server. If the
	 * test fails, consider increasing this value (in milliseconds). 
	 */
	protected static final int s_waitTime = 250;
	
	@Test
	public void testRead1() throws URISyntaxException, InterruptedException, IOException, ConnectorException
	{
		WebSocketReader wsr = new WebSocketReader(new URI("ws://localhost:51234"));
		QueueSink sink = new QueueSink(1);
		Connector.connect(wsr, sink);
		TestServer server = new TestServer(51234);
		server.start();
		WebSocketClient client = wsr.getWebSocketClient();
		client.connect();
		Thread.sleep(s_waitTime);
		Queue<Object> sink_queue = sink.getQueue(0);
		assertTrue(sink_queue.isEmpty());
		server.send("foo");
		Thread.sleep(s_waitTime);
		assertFalse(sink_queue.isEmpty());
		String received = (String) sink_queue.remove();
		assertEquals("foo", received);
		assertTrue(sink_queue.isEmpty());
		server.stop();
	}
	
	public static class TestServer extends WebSocketServer
	{
		public TestServer(int port) throws UnknownHostException
		{
			super(new InetSocketAddress(port));
		}

		@Override
		public void onClose(WebSocket arg0, int arg1, String arg2, boolean arg3)
		{
			// Do nothing
		}

		@Override
		public void onError(WebSocket arg0, Exception arg1) 
		{
			// Do nothing
			arg1.printStackTrace();
		}

		@Override
		public void onMessage(WebSocket arg0, String arg1) 
		{
			// Do nothing	
		}

		@Override
		public void onOpen(WebSocket arg0, ClientHandshake arg1) 
		{
			// Do nothing
		}
		
		/**
		 * Tells the server to send a message
		 * @param message The message to send
		 */
		public void send(String message)
		{
			Collection<WebSocket> con = connections();
			for (WebSocket socket : con)
			{
				socket.send(message);
			}
		}
	}
	
}
