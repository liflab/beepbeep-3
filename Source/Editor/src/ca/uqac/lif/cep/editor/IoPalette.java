package ca.uqac.lif.cep.editor;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;

import ca.uqac.lif.cep.FileHelper;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.cep.io.FileWriter;
import ca.uqac.lif.cep.io.StreamReader;

public class IoPalette extends Palette
{
	/**
	 * Creates the I/O palette
	 */
	public IoPalette()
	{
		super();
		setName("I/O");
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
			super("Stream reader", FileHelper.internalFileToBytes(IoPalette.class, "StreamReader.png"));
		}

		@Override
		public EditorBox newEditorBox() 
		{
			try 
			{
				return new StreamReaderEditorBox(new StreamReader(new FileInputStream(new File("foo.csv"))), image);
			} 
			catch (FileNotFoundException e)
			{
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			return null;
		}
		
		protected static class StreamReaderEditorBox extends EditorBox
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
			super("File writer", FileHelper.internalFileToBytes(IoPalette.class, "FileWriter.png"));
		}

		@Override
		public EditorBox newEditorBox() 
		{
			return new FileWriterEditorBox(new FileWriter(new File("out.txt"), false), image);
		}
		
		protected static class FileWriterEditorBox extends EditorBox
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