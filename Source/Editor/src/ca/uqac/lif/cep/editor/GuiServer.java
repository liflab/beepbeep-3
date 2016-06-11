/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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
package ca.uqac.lif.cep.editor;

import ca.uqac.lif.jerrydog.InnerFileServer;

public class GuiServer extends InnerFileServer 
{

	/**
	 * Instantiates a new GUI server
	 */
	public GuiServer() 
	{
		super(GuiServer.class);
		setServerPort(31313);
		setUserAgent("BeepBeep 3 editor");
	}

	public static void main(String[] args)
	{
		GuiServer server = new GuiServer();
		server.startServer();
		while (true)
		{
			sleep(10000);
		}
	}

	public static void sleep(long d)
	{
		try 
		{
			Thread.sleep(d);
		} 
		catch (InterruptedException e) 
		{
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

}
