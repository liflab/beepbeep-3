package ca.uqac.lif.cep.xml;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.xml.TextElement;
import ca.uqac.lif.xml.XPathExpression;
import ca.uqac.lif.xml.XmlElement;

/**
 * Utility function to evaluate an XPath expression, ending with 
 * a <code>text()</code> element
 */
public class XPathFunctionGetText extends XPathFunctionGet<String>
{	
	public XPathFunctionGetText(String exp)
	{
		super(exp, String.class);
	}
	
	public XPathFunctionGetText(XPathExpression exp)
	{
		super(exp, String.class);
	}

	@Override
	public String castValue(XmlElement e)
	{
		if (e instanceof TextElement)
		{
			return ((TextElement) e).getText();
		}
		return "";
	}
	
	@Override
	public XPathFunctionGetText clone(Context context)
	{
		XPathExpression exp = XPathFunction.evaluatePlaceholders(m_expression, context);
		XPathFunctionGetText out = new XPathFunctionGetText(exp);
		return out;
	}
}