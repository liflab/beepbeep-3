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

import ca.uqac.lif.jerrydog.CallbackResponse;
import ca.uqac.lif.jerrydog.CallbackResponse.ContentType;
import ca.uqac.lif.jerrydog.RequestCallback;

public class GetImage extends EditorCallback
{
	public GetImage(Editor editor)
	{
		super(RequestCallback.Method.GET, "/image", editor);
	}

	@Override
	public CallbackResponse process(HttpExchange t)
	{
		CallbackResponse response = new CallbackResponse(t);
		Map<String,String> params = getParameters(t);
		int proc_id = Integer.parseInt(params.get("id"));
		EditorBox box = m_editor.getBox(proc_id);
		if (box == null)
		{
			// Box not found
			response.setCode(CallbackResponse.HTTP_NOT_FOUND);
			return response;
		}
		byte[] image = box.getImage();
		if (image == null)
		{
			// No image
			response.setCode(CallbackResponse.HTTP_NOT_FOUND);
			return response;
		}
		response.setCode(CallbackResponse.HTTP_OK);
		response.setContentType(ContentType.PNG);
		response.setContents(image);
		return response;
	}
}
