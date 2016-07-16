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

import ca.uqac.lif.cep.Palette;
import ca.uqac.lif.cep.Palette.PaletteEntry;
import ca.uqac.lif.jerrydog.CallbackResponse;
import ca.uqac.lif.jerrydog.RequestCallback;
import ca.uqac.lif.jerrydog.CallbackResponse.ContentType;

import com.sun.net.httpserver.HttpExchange;

public class PaletteButton extends EditorCallback
{
	public PaletteButton(Editor editor)
	{
		super(RequestCallback.Method.GET, "/palette-button", editor);
	}

	@Override
	public CallbackResponse process(HttpExchange t)
	{
		CallbackResponse response = new CallbackResponse(t);
		Map<String,String> params = getParameters(t);
		int palette_id = Integer.parseInt(params.get("id").trim());
		int button_nb = Integer.parseInt(params.get("nb").trim());
		Palette pal = m_editor.getPalette(palette_id);
		if (pal == null)
		{
			// Palette not found
			response.setCode(CallbackResponse.HTTP_NOT_FOUND);
			return response;
		}
		PaletteEntry entry = pal.getEntry(button_nb);
		if (entry == null)
		{
			// Entry not found
			response.setCode(CallbackResponse.HTTP_NOT_FOUND);
			return response;
		}
		byte[] image = entry.m_image;
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
