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

import java.util.List;

import ca.uqac.lif.jerrydog.CallbackResponse;
import ca.uqac.lif.jerrydog.RequestCallback;
import ca.uqac.lif.jerrydog.CallbackResponse.ContentType;

import com.sun.net.httpserver.HttpExchange;

public class GetPalettes extends EditorCallback 
{
	public GetPalettes(Editor editor)
	{
		super(RequestCallback.Method.GET, "/palettes", editor);
	}

	@Override
	public CallbackResponse process(HttpExchange t) 
	{
		CallbackResponse response = new CallbackResponse(t);
		List<Palette> palettes = m_editor.getPalettes();
		StringBuilder out = new StringBuilder(); 
		out.append("[");
		for (int i = 0; i < palettes.size(); i++)
		{
			if (i > 0)
			{
				out.append(",");
			}
			Palette pal = palettes.get(i);
			out.append(pal.toJson());
		}
		out.append("]");
		response.setCode(CallbackResponse.HTTP_OK);
		response.setContentType(ContentType.JSON);
		response.setContents(out.toString());
		return response;
	}
}
