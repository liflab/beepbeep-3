package ca.uqac.lif.cep.editor;

import ca.uqac.lif.jerrydog.RestCallback;

public abstract class EditorCallback extends RestCallback 
{
	protected GuiServer m_editor;
	
	public EditorCallback(Method m, String path, GuiServer editor)
	{
		super(m, path);
		m_editor = editor;
	}
}
