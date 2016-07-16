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

import ca.uqac.lif.cep.ProcessorBox;
import ca.uqac.lif.cep.ProcessorSettings;
import ca.uqac.lif.cep.Palette;
import ca.uqac.lif.cep.Palette.PaletteEntry;
import ca.uqac.lif.jerrydog.CallbackResponse;
import ca.uqac.lif.jerrydog.CallbackResponse.ContentType;
import ca.uqac.lif.jerrydog.RequestCallback;

public class GetSettings extends EditorCallback
{
	public GetSettings(Editor editor)
	{
		super(RequestCallback.Method.GET, "/settings", editor);
	}

	@Override
	public CallbackResponse process(HttpExchange t)
	{
		CallbackResponse response = new CallbackResponse(t);
		Map<String,String> params = getParameters(t);
		int palette_id = Integer.parseInt(params.get("palette").trim());
		Palette palette = m_editor.getPalette(palette_id);
		if (palette == null)
		{
			// Palette not found
			response.setCode(CallbackResponse.HTTP_NOT_FOUND);
			return response;
		}
		int button_id = Integer.parseInt(params.get("button").trim());
		PaletteEntry entry = palette.getEntry(button_id);
		if (entry == null)
		{
			// Entry not found
			response.setCode(CallbackResponse.HTTP_NOT_FOUND);
			return response;
		}
		ProcessorSettings settings = entry.getSettings();
		ProcessorBox box = entry.newEditorBox(settings);
		response.setCode(CallbackResponse.HTTP_OK);
		response.setContentType(ContentType.JSON);
		response.setContents(box.toJson().toString());
		return response;
	}
}
