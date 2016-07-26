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
import ca.uqac.lif.cep.Palette;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorBox;
import ca.uqac.lif.cep.ProcessorSettings;

public class PackageExtension extends Palette
{
	public PackageExtension()
	{
		super(PackageExtension.class, "Linear Temporal Logic palette\n"
				+ "(C) 2015-2016 Sylvain Hallé, Université du Québec à Chicoutim");
		add(new AndPaletteEntry());
		add(new OrPaletteEntry());
		add(new NextPaletteEntry());
		add(new NotPaletteEntry());
		add(new EventuallyPaletteEntry());
		add(new GloballyPaletteEntry());
		add(new UntilPaletteEntry());
	}
	
	/**
	 * Palette entry to create a new instance of AND
	 */
	protected static class AndPaletteEntry extends PaletteEntry
	{
		public AndPaletteEntry()
		{
			super("And", TrooleanAnd.class, FileHelper.internalFileToBytes(PackageExtension.class, "And.png"));
		}

		@Override
		public ProcessorBox newEditorBox(ProcessorSettings settings) 
		{
			return new BinaryProcessorBox(new TrooleanAnd(), m_image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of OR
	 */
	protected static class OrPaletteEntry extends PaletteEntry
	{
		public OrPaletteEntry()
		{
			super("Or", TrooleanOr.class, FileHelper.internalFileToBytes(PackageExtension.class, "Or.png"));
		}

		@Override
		public ProcessorBox newEditorBox(ProcessorSettings settings)
		{
			return new BinaryProcessorBox(new TrooleanOr(), m_image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of U
	 */
	protected static class UntilPaletteEntry extends PaletteEntry
	{
		public UntilPaletteEntry()
		{
			super("Until", Until.class, FileHelper.internalFileToBytes(PackageExtension.class, "Until.png"));
		}

		@Override
		public ProcessorBox newEditorBox(ProcessorSettings settings)
		{
			return new BinaryProcessorBox(new Until(), m_image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of NOT
	 */
	protected static class NotPaletteEntry extends PaletteEntry
	{
		public NotPaletteEntry()
		{
			super("Not", TrooleanNot.class, FileHelper.internalFileToBytes(PackageExtension.class, "Not.png"));
		}

		@Override
		public ProcessorBox newEditorBox(ProcessorSettings settings)
		{
			return new UnaryProcessorBox(new TrooleanNot(), m_image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of F
	 */
	protected static class EventuallyPaletteEntry extends PaletteEntry
	{
		public EventuallyPaletteEntry()
		{
			super("Eventually", Eventually.class, FileHelper.internalFileToBytes(PackageExtension.class, "Eventually.png"));
		}

		@Override
		public ProcessorBox newEditorBox(ProcessorSettings settings)
		{
			return new UnaryProcessorBox(new Eventually(), m_image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of G
	 */
	protected static class GloballyPaletteEntry extends PaletteEntry
	{
		public GloballyPaletteEntry()
		{
			super("Globally", Globally.class, FileHelper.internalFileToBytes(PackageExtension.class, "Globally.png"));
		}

		@Override
		public ProcessorBox newEditorBox(ProcessorSettings settings)
		{
			return new UnaryProcessorBox(new Globally(), m_image);
		}
	}
	
	/**
	 * Palette entry to create a new instance of X
	 */
	protected static class NextPaletteEntry extends PaletteEntry
	{
		public NextPaletteEntry()
		{
			super("Next", Next.class, FileHelper.internalFileToBytes(PackageExtension.class, "Next.png"));
		}

		@Override
		public ProcessorBox newEditorBox(ProcessorSettings settings)
		{
			return new UnaryProcessorBox(new Next(), m_image);
		}
	}

	/**
	 * Generic editor box for all palette entries with a binary processor
	 */
	protected static class BinaryProcessorBox extends ProcessorBox
	{
		public BinaryProcessorBox(Processor p, byte[] image) 
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
	protected static class UnaryProcessorBox extends ProcessorBox
	{
		public UnaryProcessorBox(Processor p, byte[] image) 
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
