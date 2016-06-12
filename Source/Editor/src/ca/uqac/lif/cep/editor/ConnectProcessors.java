package ca.uqac.lif.cep.editor;

import java.util.Map;

import ca.uqac.lif.cep.Connector;
import ca.uqac.lif.cep.EditorBox;
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
		Connector.connect(out_p, in_p, out_nb, in_nb);
		response.setCode(CallbackResponse.HTTP_OK);
		return response;
	}

}
