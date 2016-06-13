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

import ca.uqac.lif.cep.EditorBox.Coordinate.Orientation;

/**
 * Information about the graphical representation of a processor in
 * an editor.
 * <p>
 * Editorial choice: it could be easier to use <tt>BufferedImage</tt>s
 * instead of byte arrays for processor pictures. However, this would impose
 * a dependency on the <tt>java.awt</tt> package, just for a single object
 * we don't manipulate or display anyway.
 * @author Sylvain Hallé
 */
public class EditorBox 
{
	/**
	 * The processor linked to this box
	 */
	protected Processor m_processor;
	
	/**
	 * The image used to represent a processor
	 */
	protected byte[] m_image;
	
	/**
	 * The height of the image, in pixels
	 */
	protected int m_height = 0;
	
	/**
	 * The width of the image, in pixels
	 */
	protected int m_width = 0;
	
	/**
	 * The x position of the box in the editor
	 */
	protected int m_x = 0;
	
	/**
	 * The y position of the box in the editor
	 */
	protected int m_y = 0;

	/**
	 * The location of each input point in the image
	 */
	protected Coordinate[] m_inputPoints;
	
	/**
	 * The location of each input point in the image
	 */
	protected Coordinate[] m_outputPoints;
	
	/**
	 * Image used to represent a generic 0:1 processor
	 */
	public static final transient byte[] s_image01;
	
	/**
	 * Image used to represent a generic 1:0 processor
	 */
	public static final transient byte[] s_image10;
	
	/**
	 * Image used to represent a generic 1:1 processor
	 */
	public static final transient byte[] s_image11;
	
	/**
	 * Image used to represent a generic 2:1 processor
	 */
	public static final transient byte[] s_image21;
	
	/* Initialize the images */
	static
	{
		s_image01 = FileHelper.internalFileToBytes(EditorBox.class, "processor-0-1.png");
		s_image10 = FileHelper.internalFileToBytes(EditorBox.class, "processor-1-0.png");
		s_image11 = FileHelper.internalFileToBytes(EditorBox.class, "processor-1-1.png");
		s_image21 = FileHelper.internalFileToBytes(EditorBox.class, "processor-2-1.png");
	}
	
	/**
	 * Creates an empty editor box, with all its fields uninitialized.
	 * This should only be called by the class' inner members.
	 * @param p The processor linked to this box
	 */
	public EditorBox(Processor p)
	{
		this(p, null);
	}
	
	/**
	 * Creates a new editor box
	 * @param p The processor linked to this box
	 * @param image The image used to represent a processor
	 */
	public EditorBox(Processor p, byte[] image)
	{
		super();
		m_processor = p;
		m_image = image;
		m_inputPoints = new Coordinate[0];
		m_outputPoints = new Coordinate[0];
	}
	
	/**
	 * Sets the image used to represent a processor
	 * @param image The image
	 * @return This box
	 */
	public EditorBox setImage(byte[] image)
	{
		m_image = image;
		return this;
	}
	
	/**
	 * Gets the image used to represent a processor
	 * @return The image
	 */
	public byte[] getImage()
	{
		return m_image;
	}
	
	/**
	 * Sets the coordinates of each input in the processor's
	 * picture
	 * @param coordinates The coordinates
	 * @return This box
	 */
	public EditorBox setInputPoints(Coordinate[] coordinates)
	{
		m_inputPoints = coordinates;
		return this;
	}
	
	/**
	 * Sets the coordinates of each output in the processor's
	 * picture
	 * @param coordinates The coordinates
	 * @return This box
	 */
	public EditorBox setOutputPoints(Coordinate[] coordinates)
	{
		m_outputPoints = coordinates;
		return this;
	}
	
	/**
	 * Sets the dimensions of the picture
	 * @param width The width in pixels
	 * @param height The height in pixels
	 * @return This box
	 */
	public EditorBox setSize(int width, int height)
	{
		m_width = width;
		m_height = height;
		return this;
	}
	
	/**
	 * Gets the processor associated to this box
	 * @return The processor
	 */
	public Processor getProcessor()
	{
		return m_processor;
	}
	
	/**
	 * Sets the x position of this box
	 * @param x The position
	 * @return This box
	 */
	public EditorBox setX(int x)
	{
		m_x = x;
		return this;
	}
	
	/**
	 * Sets the y position of this box
	 * @param y The position
	 * @return This box
	 */
	public EditorBox setY(int y)
	{
		m_y = y;
		return this;
	}
	
	/**
	 * Creates a JSON rendition of this editor box
	 * @return A well-formed JSON string
	 */
	public String toJson()
	{
		StringBuilder out = new StringBuilder();
		out.append("{");
		out.append("\"id\":").append(m_processor.getId()).append(",");
		out.append("\"name\": \"").append(getProcessorName()).append("\",");
		out.append("\"width\":").append(m_width).append(",");
		out.append("\"height\":").append(m_height).append(",");
		out.append("\"inputs\":[");
		for (int i = 0; i < m_inputPoints.length; i++)
		{
			if (i > 0)
			{
				out.append(",");
			}
			out.append(m_inputPoints[i].toJson());
		}
		out.append("],");
		out.append("\"outputs\":[");
		for (int i = 0; i < m_outputPoints.length; i++)
		{
			if (i > 0)
			{
				out.append(",");
			}
			out.append(m_outputPoints[i].toJson());
		}
		out.append("]");
		out.append("}");
		return out.toString();
	}
	
	protected String getProcessorName()
	{
		String class_name = m_processor.getClass().getName();
		String[] parts = class_name.split("\\.");
		return parts[parts.length - 1];
	}
	
	/**
	 * Representation of a pixel in an image
	 */
	public static class Coordinate
	{
		public static enum Orientation {UP, DOWN, LEFT, RIGHT};
		
		public int x;
		public int y;
		public Orientation orientation;
		
		public Coordinate(int x, int y, Orientation o)
		{
			super();
			this.x = x;
			this.y = y;
			this.orientation = o;
		}
		
		/**
		 * Creates a JSON rendition of this coordinate
		 * @return A well-formed JSON string
		 */
		public String toJson()
		{
			StringBuilder out = new StringBuilder();
			out.append("{");
			out.append("\"x\":").append(x).append(",");
			out.append("\"y\":").append(y).append(",");
			out.append("\"o\":\"").append(orientation).append("\"");
			out.append("}");
			return out.toString();
		}
	}
	
	public static class GenericEditorBox extends EditorBox
	{
		public GenericEditorBox(Processor p, int in_arity, int out_arity)
		{
			super(p);
			// Select an appropriate picture depending on the in/out
			// arity of the target processor
			if (in_arity == 0)
			{
				if (out_arity == 1)
				{
					// 0:1 processor
					setSize(91, 67);
					setImage(s_image01);
					Coordinate[] outputs = {
							new Coordinate(80, 34, Orientation.RIGHT)
						};
					setOutputPoints(outputs);
				}
			}
			else if (in_arity == 1)
			{
				if (out_arity == 0)
				{
					// 1:0 processor
					setSize(94, 67);
					setImage(s_image10);
					Coordinate[] inputs = {
							new Coordinate(11, 34, Orientation.LEFT)
						};
					setInputPoints(inputs);
				}
				else if (out_arity == 1)
				{
					// 1:1 processor
					setSize(126, 67);
					setImage(s_image11);
					Coordinate[] inputs = {
						new Coordinate(11, 34, Orientation.LEFT)
					};
					Coordinate[] outputs = {
							new Coordinate(115, 34, Orientation.RIGHT)
						};
					setInputPoints(inputs);
					setOutputPoints(outputs);
				}				
			}
			else if (in_arity == 2)
			{
				if (out_arity == 1)
				{
					// 2:1 processor
					setSize(126, 67);
					setImage(s_image21);
					Coordinate[] inputs = {
						new Coordinate(30, 10, Orientation.UP),
						new Coordinate(30, 120, Orientation.DOWN)
					};
					Coordinate[] outputs = {
							new Coordinate(80, 65, Orientation.RIGHT)
						};
					setInputPoints(inputs);
					setOutputPoints(outputs);
				}				
			}
		}
	}
}
