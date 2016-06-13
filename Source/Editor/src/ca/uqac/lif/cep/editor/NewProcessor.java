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
package ca.uqac.lif.cep.editor;

import java.util.Map;

import com.sun.net.httpserver.HttpExchange;

import ca.uqac.lif.cep.EditorBox;
import ca.uqac.lif.jerrydog.CallbackResponse;
import ca.uqac.lif.jerrydog.CallbackResponse.ContentType;
import ca.uqac.lif.jerrydog.RequestCallback;

public class NewProcessor extends EditorCallback
{
	public NewProcessor(Editor editor)
	{
		super(RequestCallback.Method.POST, "/processor", editor);
	}

	@Override
	public CallbackResponse process(HttpExchange t)
	{
		CallbackResponse response = new CallbackResponse(t);
		Map<String,String> params = getParameters(t);
		String type = params.get("type").trim();
		EditorBox box = m_editor.createNewProcessor(type);
		if (params.containsKey("x") && params.containsKey("y"))
		{
			box.setX(Float.parseFloat(params.get("x").trim()));
			box.setY(Float.parseFloat(params.get("y").trim()));
		}
		response.setCode(CallbackResponse.HTTP_OK);
		response.setContentType(ContentType.JSON);
		response.setContents(box.toJson());
		return response;
	}

}
