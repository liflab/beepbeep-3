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

import java.util.HashSet;
import java.util.Set;

import ca.uqac.lif.cep.EditorBox;
import ca.uqac.lif.cep.Passthrough;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.jerrydog.InnerFileServer;

public class Editor extends InnerFileServer 
{
	protected Set<EditorBox> m_boxes;
	
	protected static transient final String s_processorImageFolder = "resource/images/processors";

	/**
	 * Instantiates a new GUI server
	 */
	public Editor() 
	{
		super(Editor.class);
		m_boxes = new HashSet<EditorBox>();
		setServerPort(31313);
		setUserAgent("BeepBeep 3 editor");
		registerCallback(0, new GetImage(this));
		registerCallback(0, new NewProcessor(this));
		registerCallback(0, new ConnectProcessors(this));
		registerCallback(0, new MoveBox(this));
	}

	public static void main(String[] args)
	{
		Editor server = new Editor();
		server.startServer();
		while (true)
		{
			sleep(10000);
		}
	}

	/**
	 * Sleep for some time
	 * @param d The time (in ms)
	 */
	public static void sleep(long d)
	{
		try 
		{
			Thread.sleep(d);
		} 
		catch (InterruptedException e) 
		{
			e.printStackTrace();
		}
	}

	/**
	 * Instantiates a new processor, and returns a JSON element used to
	 * display it in the editor
	 * @param type The type of processor to instantiate
	 * @return An editor box for this new processor
	 */
	public EditorBox createNewProcessor(String type)
	{
		Processor p = null;
		if (type.compareToIgnoreCase("ca.uqac.lif.cep.Passthrough") == 0)
		{
			p = new Passthrough(1);
		}
		else if (type.compareToIgnoreCase("ca.uqac.lif.cep.ltl.And") == 0)
		{
			p = new ca.uqac.lif.cep.ltl.And();
		}
		EditorBox box = p.getEditorBox();
		m_boxes.add(box);
		return box;
	}
	
	/**
	 * Retrieves the instance of processor with given ID
	 * @param id The ID
	 * @return The processor, or null if not found
	 */
	public EditorBox getBox(int id)
	{
		for (EditorBox p : m_boxes)
		{
			if (p.getProcessor().getId() == id)
			{
				return p;
			}
		}
		return null;
	}
}
