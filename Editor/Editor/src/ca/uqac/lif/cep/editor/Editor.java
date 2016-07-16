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
package ca.uqac.lif.cep.editor;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import ca.uqac.lif.cep.ProcessorBox;
import ca.uqac.lif.cep.interpreter.Palette;
import ca.uqac.lif.jerrydog.InnerFileServer;

public class Editor extends InnerFileServer 
{
	protected Set<ProcessorBox> m_boxes;
	
	protected List<Palette> m_palettes;
	
	protected static transient final String s_processorImageFolder = "resource/images/processors";

	/**
	 * Instantiates a new GUI server
	 */
	public Editor() 
	{
		super(Editor.class);
		m_boxes = new HashSet<ProcessorBox>();
		m_palettes = new LinkedList<Palette>();
		setServerPort(31313);
		setUserAgent("BeepBeep 3 editor");
		registerCallback(0, new GetImage(this));
		registerCallback(0, new NewProcessor(this));
		registerCallback(0, new ConnectProcessors(this));
		registerCallback(0, new MoveBox(this));
		registerCallback(0, new GetPalettes(this));
		registerCallback(0, new PaletteButton(this));
		registerCallback(0, new GetSettings(this));
	}
	
	/**
	 * Gets the list of all palettes created for this editor
	 * @return The list of palettes
	 */
	public List<Palette> getPalettes()
	{
		return m_palettes;
	}
	
	/**
	 * Adds a palette to this editor
	 * @param pal The palette
	 * @return This editor
	 */
	public Editor add(Palette pal)
	{
		m_palettes.add(pal);
		return this;
	}
	
	/**
	 * Gets the palette with given ID
	 * @param id The palette ID
	 * @return The palette
	 */
	public Palette getPalette(int id)
	{
		return m_palettes.get(id);
	}
	
	/**
	 * Adds a new editor box to this editor
	 * @param box The box
	 * @return This editor
	 */
	public Editor add(ProcessorBox box)
	{
		m_boxes.add(box);
		return this;
	}
	
	/**
	 * Retrieves the instance of processor with given ID
	 * @param id The ID
	 * @return The processor, or null if not found
	 */
	public ProcessorBox getBox(int id)
	{
		for (ProcessorBox p : m_boxes)
		{
			if (p.getProcessor().getId() == id)
			{
				return p;
			}
		}
		return null;
	}
}
