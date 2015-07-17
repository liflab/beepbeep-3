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
package ca.uqac.lif.cep.interpreter;

import java.util.HashMap;
import java.util.Map;

import ca.uqac.lif.util.PackageFileReader;

/**
 * Provides extensions to the original parser's grammar
 */
public abstract class GrammarExtension
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
	protected static final String s_commentChar = "#";
	
	/**
	 * A reference to the current class of grammar extension. This is
	 * necessary because the methods {@link #getAssociations()} and
	 * {@link #getGrammar()} must read a file whose path is relative to
	 * <em>that</em> class, and not the {@link GrammarExtension} class. 
	 */
	protected final Class<? extends GrammarExtension> m_classReference;
	
	/**
	 * Instantiates a grammar extension
	 * @param reference The current grammar extension
	 */
	protected GrammarExtension(Class<? extends GrammarExtension> reference)
	{
		super();
		m_classReference = reference;
	}
	
	/**
	 * Returns a map of associations between non-terminal symbols of the
	 * grammar and fully-qualified class names.
	 * @return The map
	 */
	public final Map<String,String> getAssociations()
	{
		Map<String,String> out = new HashMap<String,String>();
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
			out.put(non_terminal, class_name);
		}
		return out;
	}
	
	public final String getGrammar()
	{
		String file_contents = PackageFileReader.readPackageFile(m_classReference, s_grammarFilename);
		return file_contents;
	}
}
