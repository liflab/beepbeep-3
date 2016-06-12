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
		response.setCode(CallbackResponse.HTTP_OK);
		response.setContentType(ContentType.JSON);
		response.setContents(box.toJson());
		return response;
	}

}
