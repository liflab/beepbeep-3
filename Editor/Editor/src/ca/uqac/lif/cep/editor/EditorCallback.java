package ca.uqac.lif.cep.editor;

import ca.uqac.lif.azrael.json.JsonSerializer;
import ca.uqac.lif.jerrydog.RestCallback;
import ca.uqac.lif.json.JsonParser;

public abstract class EditorCallback extends RestCallback 
{
	protected Editor m_editor;
	
	protected JsonParser m_parser;
	
	protected JsonSerializer m_serializer = new JsonSerializer();
	
	public EditorCallback(Method m, String path, Editor editor)
	{
		super(m, path);
		m_editor = editor;
		m_parser = new JsonParser();
	}
}
