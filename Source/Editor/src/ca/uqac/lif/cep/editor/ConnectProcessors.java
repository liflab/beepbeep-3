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

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.Connector.ConnectorException;
import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.jerrydog.CallbackResponse;
import ca.uqac.lif.jerrydog.RequestCallback;

import com.sun.net.httpserver.HttpExchange;

public class ConnectProcessors extends EditorCallback 
{
	public ConnectProcessors(Editor editor)
	{
		super(RequestCallback.Method.POST, "/connect", editor);
	}

	@Override
	public CallbackResponse process(HttpExchange t) 
	{
		CallbackResponse response = new CallbackResponse(t);
		Map<String,String> params = getParameters(t);
		int in_id = Integer.parseInt(params.get("input-id").trim());
		int in_nb = Integer.parseInt(params.get("input-nb").trim());
		int out_id = Integer.parseInt(params.get("output-id").trim());
		int out_nb = Integer.parseInt(params.get("output-nb").trim());
		EditorBox in_box = m_editor.getBox(in_id);
		EditorBox out_box = m_editor.getBox(out_id);
		if (in_box == null || out_box == null)
		{
			// Box not found
			response.setCode(CallbackResponse.HTTP_NOT_FOUND);
			return response;
		}
		Processor in_p = in_box.getProcessor();
		Processor out_p = out_box.getProcessor();
		try 
		{
			Connector.connect(out_p, in_p, out_nb, in_nb);
			response.setCode(CallbackResponse.HTTP_OK);
		}
		catch (ConnectorException e) 
		{
			response.setCode(CallbackResponse.HTTP_BAD_REQUEST);
			response.setContents(e.getMessage());
		}
		return response;
	}

}
