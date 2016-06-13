package ca.uqac.lif.cep.editor;

import java.util.Map;

import com.sun.net.httpserver.HttpExchange;

import ca.uqac.lif.cep.EditorBox;
import ca.uqac.lif.jerrydog.CallbackResponse;
import ca.uqac.lif.jerrydog.RequestCallback;

public class MoveBox extends EditorCallback
{
	public MoveBox(Editor editor)
	{
		super(RequestCallback.Method.POST, "/move", editor);
	}

	@Override
	public CallbackResponse process(HttpExchange t)
	{
		CallbackResponse response = new CallbackResponse(t);
		Map<String,String> params = getParameters(t);
		int proc_id = Integer.parseInt(params.get("id").trim());
		int x = Integer.parseInt(params.get("x").trim());
		int y = Integer.parseInt(params.get("y").trim());
		EditorBox box = m_editor.getBox(proc_id);
		if (box == null)
		{
			// Box not found
			response.setCode(CallbackResponse.HTTP_NOT_FOUND);
			return response;
		}
		box.setX(x).setY(y);
		response.setCode(CallbackResponse.HTTP_OK);
		return response;
	}
}
