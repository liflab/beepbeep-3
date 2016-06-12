package ca.uqac.lif.cep.editor;

import java.util.Map;

import com.sun.net.httpserver.HttpExchange;

import ca.uqac.lif.cep.EditorBox;
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
