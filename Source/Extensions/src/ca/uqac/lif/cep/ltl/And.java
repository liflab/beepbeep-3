/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2015 Sylvain Hallé

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

import java.util.Stack;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.EditorBox;
import ca.uqac.lif.cep.EditorBox.Coordinate;
import ca.uqac.lif.cep.FileHelper;
import ca.uqac.lif.cep.FunctionProcessor;
import ca.uqac.lif.cep.Processor;

public class And extends FunctionProcessor 
{
	protected static final transient byte[] s_image = FileHelper.internalFileToBytes(And.class, "And.png");
	
	public And()
	{
		super(Troolean.AND_FUNCTION);
	}
	
	public static void build(Stack<Object> stack) 
	{
		stack.pop(); // (
		Processor right = (Processor) stack.pop();
		stack.pop(); // )
		stack.pop(); // op
		stack.pop(); // (
		Processor left = (Processor) stack.pop();
		stack.pop(); // )
		And op = new And();
		Connector.connect(left, op, 0, 0);
		Connector.connect(right, op, 0, 1);
		stack.push(op);
	}

	@Override
	public And clone()
	{
		return new And();
	}
	
	@Override
	public EditorBox getEditorBox()
	{
		EditorBox box = new EditorBox(this, s_image);
		box.setSize(61, 76);
		Coordinate[] inputs = {
				new Coordinate(22, 10, Coordinate.Orientation.UP),
				new Coordinate(22, 67, Coordinate.Orientation.DOWN)
		};
		Coordinate[] outputs = {
				new Coordinate(52, 40, Coordinate.Orientation.RIGHT)
		};
		box.setInputPoints(inputs);
		box.setOutputPoints(outputs);
		return box;
	}

}
