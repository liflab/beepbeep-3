package ca.uqac.lif.cep.editor;

import java.util.Map;

import com.sun.net.httpserver.HttpExchange;

import ca.uqac.lif.cep.Processor;
import ca.uqac.lif.jerrydog.CallbackResponse;
import ca.uqac.lif.jerrydog.CallbackResponse.ContentType;
import ca.uqac.lif.jerrydog.RequestCallback;

public class GetImage extends EditorCallback
{
	public GetImage(GuiServer editor)
	{
		super(RequestCallback.Method.GET, "/image", editor);
	}

	@Override
	public CallbackResponse process(HttpExchange t)
	{
		CallbackResponse response = new CallbackResponse(t);
		Map<String,String> params = getParameters(t);
		int proc_id = Integer.parseInt(params.get("id"));
		Processor p = m_editor.getProcessor(proc_id);
		if (p == null)
		{
			// Processor not found
			response.setCode(CallbackResponse.HTTP_NOT_FOUND);
			return response;
		}
		byte[] image = p.getImage();
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
