package ca.uqac.lif.cep.editor;

import java.util.Map;

import com.sun.net.httpserver.HttpExchange;

import ca.uqac.lif.jerrydog.CallbackResponse;
import ca.uqac.lif.jerrydog.CallbackResponse.ContentType;
import ca.uqac.lif.jerrydog.RequestCallback;
import ca.uqac.lif.json.JsonMap;

public class NewProcessor extends EditorCallback
{
	public NewProcessor(GuiServer editor)
	{
		super(RequestCallback.Method.POST, "/processor", editor);
	}

	@Override
	public CallbackResponse process(HttpExchange t)
	{
		CallbackResponse response = new CallbackResponse(t);
		Map<String,String> params = getParameters(t);
		String type = params.get("type").trim();
		JsonMap out = m_editor.createNewProcessor(type);
		response.setCode(CallbackResponse.HTTP_OK);
		response.setContentType(ContentType.JSON);
		response.setContents(out.toString());
		return response;
	}

}
