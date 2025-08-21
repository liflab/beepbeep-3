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
package ca.uqac.lif.cep.util;

import java.io.BufferedWriter;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.junit.Test;

/**
 * A number of helpful utilities to read, write and manage files
 *
 */
public class FileHelper
{
	/**
	 * The system-dependent carriage return symbol
	 */
	public static final String CRLF = System.getProperty("line.separator");

	/**
	 * Utility classes should not have public constructors. We make an
	 * exception as this class is part of a jUnit folder.
	 */
	public FileHelper()
	{
		// Nothing to do
	}
	
	@Test
	public void dummyTest()
	{
		// This is a dummy test to avoid jUnit complaining about
		// "no runnable methods" for this file
	}

	/**
	 * Reads an input stream and puts its contents into a string
	 * @param is The input stream
	 * @return The contents
	 */
	public static String readToString(InputStream is)
	{
		String out = "";
		java.util.Scanner s = new java.util.Scanner(is);
		s.useDelimiter("\\A");
		if (s.hasNext())
		{
			out = s.next();
		}
		s.close();
		return out;
	}

	/**
	 * Reads the contents of a file and puts it into an array of bytes.
	 * @param f The file to read
	 * @return The array with the file's contents
	 */
	public static byte[] readToBytes(File f)
	{
		FileInputStream fileInputStream = null;
		int bytes_read = 0;
		byte[] bFile = new byte[(int) f.length()];
		try
		{
			//convert file into array of bytes
			fileInputStream = new FileInputStream(f);
			bytes_read = fileInputStream.read(bFile);
		}
		catch (Exception e)
		{
			Logger.getAnonymousLogger().log(Level.WARNING, "", e);
		}
		finally
		{
			if (fileInputStream != null)
			{
				try 
				{
					fileInputStream.close();
				} 
				catch (IOException e) 
				{
					Logger.getAnonymousLogger().log(Level.WARNING, "", e);
				}
			}
		}
		return Arrays.copyOf(bFile, bytes_read);
	}

	/**
	 * Writes the content of a string to a file
	 * @param f The file to write to. If the file does not exist, it will be
	 *   created
	 * @param content The content to write
	 */
	public static void writeFromString(File f, String content)
	{
		FileWriter fw = null;
		BufferedWriter bw = null;
		try
		{
			// if file doesnt exists, then create it
			if (!f.exists())
			{
				createIfNotExists(f);
			}
			fw = new FileWriter(f.getAbsoluteFile());
			bw = new BufferedWriter(fw);
			bw.write(content);
			bw.close();
		}
		catch (IOException e)
		{
			Logger.getAnonymousLogger().log(Level.WARNING, "", e);
		}
		finally
		{
			try 
			{
				if (bw != null)
				{
					bw.close();
				}
				if (fw != null)
				{
					fw.close();
				}
			} 
			catch (IOException e) 
			{
				Logger.getAnonymousLogger().log(Level.WARNING, "", e);
			}
		}
	}

	/**
	 * Creates a file and its parent directory if they do not exist
	 * @param f The file to create
	 */
	public static void createIfNotExists(File f)
	{
		File parent = f.getParentFile();
		if (parent == null)
		{
			return;
		}
		File directory = new File(parent.getAbsolutePath());
		directory.mkdirs();
	}

	/**
	 * Writes to a file from an array of bytes
	 * @param f The file to write to. If the file does not exist, it will be
	 *   created
	 * @param bFile The content to write
	 */
	public static void writeFromBytes(File f, byte[] bFile)
	{
		FileOutputStream fileOutputStream = null;
		try
		{
			// if file doesnt exists, then create it
			if (!f.exists())
			{
				createIfNotExists(f);
			}
			//convert array of bytes into file
			fileOutputStream = new FileOutputStream(f);
			fileOutputStream.write(bFile);
			
		}
		catch(Exception e)
		{
			Logger.getAnonymousLogger().log(Level.WARNING, "", e);
		}
		finally
		{
			if (fileOutputStream != null)
			{
				try 
				{
					fileOutputStream.close();
				} 
				catch (IOException e) 
				{
					Logger.getAnonymousLogger().log(Level.WARNING, "", e);
				}
			}
		}
	}

	/**
	 * Deletes a file
	 * @param filename The filename
	 * @return true if the file could be deleted, false otherwise
	 */
	public static boolean deleteFile(String filename)
	{
		File f = new File(filename);
		return f.delete();
	}

	/**
	 * Checks whether a file exists in the filesystem
	 * @param filename The filename to look for
	 * @return true if file exists, false otherwise
	 */
	public static boolean fileExists(String filename)
	{
		File f = new File(filename);
		return f.exists();
	}

	/**
	 * Replace the extension of a filename with another. For example,
	 * one can replace /my/path/foo.bar with /my/path/foo.baz.
	 * @param filename The original filename
	 * @param extension The extension to replace with
	 * @return The modified filename
	 */
	public static String replaceExtension(String filename, String extension)
	{
		String without_extension = trimExtension(filename);
		return without_extension + "." + extension;
	}

	/**
	 * Trims the extension of a filename. For example, with /my/path/foo.bar,
	 * would return /my/path/foo
	 * @param filename The filename
	 * @return The filename without the extension
	 */
	public static String trimExtension(String filename)
	{
		int position = filename.lastIndexOf('.');
		if (position < 0)
			return filename;
		return filename.substring(0, position);
	}

	public static String internalFileToString(Class<?> c, String path)
	{
		InputStream in = c.getResourceAsStream(path);
		String out;
		try
		{
			out = streamToString(in);
		}
		catch (IOException e)
		{
			Logger.getAnonymousLogger().log(Level.WARNING, "", e);
			return null;
		}
		return out;
	}

	public static byte[] internalFileToBytes(Class<?> c, String path)
	{
		InputStream in = internalFileToStream(c, path);
		byte[] file_contents = null;
		if (in != null)
		{
			file_contents = readBytes(in);
		}
		return file_contents;
	}

	public static InputStream internalFileToStream(Class<?> c, String path)
	{
		return c.getResourceAsStream(path);
	}

	/**
	 * Checks if an internal file exists
	 * @param c The reference class
	 * @param path The path of the file
	 * @return true if the file exists, false otherwise
	 */
	public static boolean internalFileExists(Class<?> c, String path)
	{
		return internalFileToStream(c, path) != null;
	}

	/**
	 * Reads a file and puts its contents in a string
	 * @param in The input stream to read
	 * @return The file's contents, and empty string if the file
	 * does not exist
	 * @throws IOException If something bad occurs
	 */
	public static String streamToString(InputStream in) throws IOException
	{
		if (in == null)
		{
			throw new IOException();
		}
		java.util.Scanner scanner = null;
		StringBuilder out = new StringBuilder();
		try
		{
			scanner = new java.util.Scanner(in, "UTF-8");
			while (scanner.hasNextLine())
			{
				String line = scanner.nextLine();
				out.append(line).append(CRLF);
			}
		}
		finally
		{
			if (scanner != null)
				scanner.close();
		}
		return out.toString();
	}

	public static byte[] readBytes(InputStream is)
	{
		int nRead;
		ByteArrayOutputStream buffer = new ByteArrayOutputStream();
		byte[] data = new byte[2048];
		try
		{
			while ((nRead = is.read(data, 0, data.length)) != -1)
			{
				buffer.write(data, 0, nRead);
			}
			buffer.flush();
		}
		catch (IOException e)
		{
			Logger.getAnonymousLogger().log(Level.WARNING, "", e);
		}
		return buffer.toByteArray();
	}

}
