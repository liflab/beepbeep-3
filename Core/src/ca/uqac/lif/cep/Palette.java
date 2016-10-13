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
package ca.uqac.lif.cep;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ca.uqac.lif.cep.objectfactory.SettingsSet;
import ca.uqac.lif.cep.util.PackageFileReader;

/**
 * Provides extensions to the original parser's grammar
 */
public abstract class Palette
{
	/**
	 * The (local) filename containing the associations between
	 * non-terminal symbols of the grammar and classes defined in that
	 * extension of the grammar
	 */
	protected static final String s_associationsFilename = "associations.txt";
	
	/**
	 * The (local) filename containing the BNF grammar to extend the
	 * interpreter's basic grammar
	 */
	protected static final String s_grammarFilename = "eml.bnf";
	
	/**
	 * The character used for comments in the associations file
	 */
	protected static final transient String s_commentChar = "#";
	
	/**
	 * The message used to describe this palette
	 */
	protected String m_message = "";
	
	/**
	 * A reference to the current class of grammar extension. This is
	 * necessary because the methods {@link #getAssociations()} and
	 * {@link #getGrammar()} must read a file whose path is relative to
	 * <em>that</em> class, and not the {@link Palette} class. 
	 */
	protected final Class<? extends Palette> m_classReference;
	
	/**
	 * The list of entries in this palette
	 */
	protected List<PaletteEntry> m_entries;
	
	/**
	 * The ID for this palette
	 */
	protected int m_id;
	
	/**
	 * A counter for palette IDs
	 */
	protected static transient int s_idCounter = 0;
	
	/**
	 * Instantiates a palette
	 * @param reference The current grammar extension
	 * @param message The short description for this grammar extension 
	 */
	protected Palette(Class<? extends Palette> reference, String message)
	{
		super();
		m_id = s_idCounter++;
		m_classReference = reference;
		m_message = message;
	}
	
	/**
	 * Returns a map of associations between non-terminal symbols of the
	 * grammar and fully-qualified class names.
	 * @return The map
	 */
	public final Map<String,Class<?>> getAssociations()
	{
		Map<String,Class<?>> out = new HashMap<String,Class<?>>();
		ClassLoader loader = getClass().getClassLoader();
		String file_contents = PackageFileReader.readPackageFile(m_classReference, s_associationsFilename);
		if (file_contents == null || file_contents.isEmpty())
		{
			return out;
		}
		String[] lines = file_contents.split("\\n");
		for (String line : lines)
		{
			line = line.trim();
			if (line.isEmpty() || line.startsWith(s_commentChar))
			{
				continue;
			}
			String[] parts = line.split(",");
			if (parts.length != 2)
			{
				// Invalid line; just ignore it
				continue;
			}
			String non_terminal = parts[0].trim();
			String class_name = parts[1].trim();
			try 
			{
				Class<?> c = loader.loadClass(class_name);
				out.put(non_terminal, c);
			} 
			catch (ClassNotFoundException e)
			{
				e.printStackTrace();
			}
		}
		return out;
	}
	
	/**
	 * Gets the BNF grammar associated to this extension
	 * @return A string containing the BNF grammar
	 */
	public final String getGrammar()
	{
		String file_contents = PackageFileReader.readPackageFile(m_classReference, s_grammarFilename);
		return file_contents;
	}
	
	/**
	 * Produces a message (e.g. copyright info, authors, etc.) associated to 
	 * the grammar extension
	 * @return The message
	 */
	public final String getMessage()
	{
		return m_message;
	}
	
	public final List<PaletteEntry> getPalette()
	{
		return m_entries;
	}
	
	/**
	 * Adds an entry to this palette
	 * @param e The entry
	 * @return This palette
	 */
	public Palette add(PaletteEntry e)
	{
		m_entries.add(e);
		return this;
	}
	
	/**
	 * Returns a palette entry for a processor of a given name
	 * @param name The processor's class name
	 * @return The palette entry, or null if not found
	 */
	public final PaletteEntry getEntry(String name)
	{
		for (PaletteEntry e : m_entries)
		{
			if (name.compareTo(e.processorName) == 0)
			{
				return e;
			}
		}
		return null;
	}
	
	/**
	 * Returns a palette entry for a processor at a given position
	 * in the palette
	 * @param index The index of the entry
	 * @return The palette entry, or null if not found
	 */
	public final PaletteEntry getEntry(int index)
	{
		if (index < 0 || index >= m_entries.size())
		{
			return null;
		}
		return m_entries.get(index);
	}
	
	/**
	 * Represents one of the processors provided by
	 * this palette.
	 */
	public static class PaletteEntry
	{
		/**
		 * The name of the processor
		 */
		public String processorName;
		
		/**
		 * The class of the processor represented by this entry
		 */
		public Class<? extends Processor> m_processorClass;
		
		/**
		 * The image associated to the processor in the palette
		 */
		public byte[] m_image;
		
		/**
		 * Craetes a new palette entry
		 * @param name The processor's name
		 * @param processor The class of the processor represented by
		 *   this entry
		 * @param image The image associated to the processor in the palette.
		 *   This is optional and can safely be replaced by <code>null</code>.
		 */
		public PaletteEntry(String name, Class<? extends Processor> processor, byte[] image)
		{
			super();
			processorName = name;
			m_processorClass = processor;
			m_image = image;
		}
		
		/**
		 * Gets the settings associated to this palette entry.
		 * This generic method should be overridden by any processor
		 * that wishes to be instantiated through this mechanism.
		 * @return The settings
		 */
		public SettingsSet getSettings()
		{
			return new SettingsSet(Object.class);
		}
	}
}
