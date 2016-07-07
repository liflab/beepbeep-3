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
package ca.uqac.lif.cep.ltl;

import ca.uqac.lif.cep.FileHelper;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.editor.EditorBox;
import ca.uqac.lif.cep.editor.Palette;
import ca.uqac.lif.cep.editor.PaletteEntry;
import ca.uqac.lif.cep.editor.ProcessorSettings;

/**
 * Editor palette for LTL and Boolean logic processors
 * @author Sylvain Hallé
 */
public class LtlPalette extends Palette 
{
	/**
	 * Creates the LTL palette
	 */
	public LtlPalette()
	{
		super();
		setName("Logic");
		add(new AndPaletteEntry());
		add(new OrPaletteEntry());
		add(new NotPaletteEntry());
		add(new EventuallyPaletteEntry());
		add(new GloballyPaletteEntry());
		add(new NextPaletteEntry());
		add(new UntilPaletteEntry());
	}
	
	/**
	 * Palette entry to create a new instance of AND
	 */
	protected static class AndPaletteEntry extends PaletteEntry
	{
		public AndPaletteEntry()
		{
			super("And", FileHelper.internalFileToBytes(LtlPalette.class, "And.png"));
		}

		@Override
		public EditorBox newEditorBox(ProcessorSettings settings) 
		{
			return new BinaryEditorBox(new And(), image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of OR
	 */
	protected static class OrPaletteEntry extends PaletteEntry
	{
		public OrPaletteEntry()
		{
			super("Or", FileHelper.internalFileToBytes(LtlPalette.class, "Or.png"));
		}

		@Override
		public EditorBox newEditorBox(ProcessorSettings settings) 
		{
			return new BinaryEditorBox(new Or(), image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of U
	 */
	protected static class UntilPaletteEntry extends PaletteEntry
	{
		public UntilPaletteEntry()
		{
			super("Until", FileHelper.internalFileToBytes(LtlPalette.class, "Until.png"));
		}

		@Override
		public EditorBox newEditorBox(ProcessorSettings settings) 
		{
			return new BinaryEditorBox(new Until(), image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of NOT
	 */
	protected static class NotPaletteEntry extends PaletteEntry
	{
		public NotPaletteEntry()
		{
			super("Not", FileHelper.internalFileToBytes(LtlPalette.class, "Not.png"));
		}

		@Override
		public EditorBox newEditorBox(ProcessorSettings settings) 
		{
			return new UnaryEditorBox(new Not(), image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of F
	 */
	protected static class EventuallyPaletteEntry extends PaletteEntry
	{
		public EventuallyPaletteEntry()
		{
			super("Eventually", FileHelper.internalFileToBytes(LtlPalette.class, "Eventually.png"));
		}

		@Override
		public EditorBox newEditorBox(ProcessorSettings settings) 
		{
			return new UnaryEditorBox(new Eventually(), image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of G
	 */
	protected static class GloballyPaletteEntry extends PaletteEntry
	{
		public GloballyPaletteEntry()
		{
			super("Globally", FileHelper.internalFileToBytes(LtlPalette.class, "Globally.png"));
		}

		@Override
		public EditorBox newEditorBox(ProcessorSettings settings) 
		{
			return new UnaryEditorBox(new Globally(), image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of X
	 */
	protected static class NextPaletteEntry extends PaletteEntry
	{
		public NextPaletteEntry()
		{
			super("Next", FileHelper.internalFileToBytes(LtlPalette.class, "Next.png"));
		}

		@Override
		public EditorBox newEditorBox(ProcessorSettings settings) 
		{
			return new UnaryEditorBox(new Next(), image);
		}
	}

	/**
	 * Generic editor box for all palette entries with a binary processor
	 */
	protected static class BinaryEditorBox extends EditorBox
	{
		public BinaryEditorBox(Processor p, byte[] image) 
		{
			super(p, image);
			setSize(61, 76);
			Coordinate[] inputs = {
					new Coordinate(22, 10, Coordinate.Orientation.UP),
					new Coordinate(22, 67, Coordinate.Orientation.DOWN)
			};
			Coordinate[] outputs = {
					new Coordinate(52, 40, Coordinate.Orientation.RIGHT)
			};
			setInputPoints(inputs);
			setOutputPoints(outputs);
		}
	}
	
	/**
	 * Generic editor box for all palette entries with an unary processor
	 */
	protected static class UnaryEditorBox extends EditorBox
	{
		public UnaryEditorBox(Processor p, byte[] image) 
		{
			super(p, image);
			setSize(87, 44);
			Coordinate[] inputs = {
					new Coordinate(7, 21, Coordinate.Orientation.LEFT),
			};
			Coordinate[] outputs = {
					new Coordinate(78, 21, Coordinate.Orientation.RIGHT)
			};
			setInputPoints(inputs);
			setOutputPoints(outputs);
		}
	}
}
