package ca.uqac.lif.cep.editor;

public abstract class PaletteEntry
{
	/**
	 * The name of the processor
	 */
	public String processorName;
	
	/**
	 * The image associated to it in the palette
	 */
	public byte[] image;
	
	public PaletteEntry(String name, byte[] img)
	{
		super();
		processorName = name;
		image = img;
	}
	
	public String toJson()
	{
		return "{\"processorname\":\"" + processorName + "\"}";
	}
	
	public ProcessorSettings getSettings()
	{
		return new ProcessorSettings();
	}
	
	public abstract EditorBox newEditorBox(ProcessorSettings settings);

}
