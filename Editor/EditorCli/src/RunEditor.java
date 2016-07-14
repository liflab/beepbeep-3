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
import ca.uqac.lif.cep.editor.Editor;
import ca.uqac.lif.cep.editor.IoPalette;
import ca.uqac.lif.cep.ltl.LtlPalette;

public class RunEditor 
{
	/**
	 * Runs the editor
	 * @param args Command-line arguments
	 */
	public static void main(String[] args)
	{
		Editor editor = new Editor();
		// Create palettes
		editor.add(new IoPalette());
		editor.add(new LtlPalette());
		editor.startServer();
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
}
