package ca.uqac.lif.cep.io;

import java.io.File;

import ca.uqac.lif.cep.FileHelper;
import ca.uqac.lif.cep.Palette;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.ProcessorBox;
import ca.uqac.lif.cep.ProcessorSettings;
import ca.uqac.lif.cep.ProcessorSettings.Setting;
import ca.uqac.lif.cep.ProcessorSettings.StringSetting;

public class IoPalette extends Palette
{
	/**
	 * Creates the I/O palette
	 */
	public IoPalette()
	{
		super(IoPalette.class, "I/0");
		add(new StreamReaderPaletteEntry());
		add(new FileWriterPaletteEntry());
	}
	
	/**
	 * Palette entry to create a new instance of stream reader
	 */
	protected static class StreamReaderPaletteEntry extends PaletteEntry
	{
		public StreamReaderPaletteEntry()
		{
			super("Stream reader", StreamReader.class, FileHelper.internalFileToBytes(IoPalette.class, "StreamReader.png"));
		}
		
		@Override
		public ProcessorSettings getSettings()
		{
			ProcessorSettings settings = new ProcessorSettings();
			settings.add(new StringSetting("Filename", true));
			return settings;
		}
		
		protected static class StreamReaderEditorBox extends ProcessorBox
		{
			public StreamReaderEditorBox(Processor p, byte[] image) 
			{
				super(p, image);
				setSize(107, 78);
				Coordinate[] outputs = {
						new Coordinate(95, 39, Coordinate.Orientation.RIGHT)
				};
				setOutputPoints(outputs);
			}
		}
	}
	
	/**
	 * Palette entry to create a new instance of stream reader
	 */
	protected static class FileWriterPaletteEntry extends PaletteEntry
	{
		public FileWriterPaletteEntry()
		{
			super("File writer", FileWriter.class, FileHelper.internalFileToBytes(IoPalette.class, "FileWriter.png"));
		}

		@Override
		public ProcessorBox newEditorBox(ProcessorSettings settings) 
		{
			Setting s_filename = settings.get("filename");
			String filename = (String) s_filename.getValue();
			return new FileWriterEditorBox(new FileWriter(new File(filename), false), m_image);
		}
		
		@Override
		public ProcessorSettings getSettings()
		{
			ProcessorSettings settings = new ProcessorSettings();
			settings.add(new StringSetting("filename", true));
			return settings;
		}
		
		protected static class FileWriterEditorBox extends ProcessorBox
		{
			public FileWriterEditorBox(Processor p, byte[] image) 
			{
				super(p, image);
				setSize(107, 78);
				Coordinate[] inputs = {
						new Coordinate(10, 39, Coordinate.Orientation.LEFT)
				};
				setInputPoints(inputs);
			}
		}
	}
}