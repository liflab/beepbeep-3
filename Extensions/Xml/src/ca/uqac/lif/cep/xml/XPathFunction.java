package ca.uqac.lif.cep.xml;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import ca.uqac.lif.cep.Context;
import ca.uqac.lif.cep.functions.UnaryFunction;
import ca.uqac.lif.xml.Equality;
import ca.uqac.lif.xml.Predicate;
import ca.uqac.lif.xml.Segment;
import ca.uqac.lif.xml.TextElement;
import ca.uqac.lif.xml.TextSegment;
import ca.uqac.lif.xml.XPathExpression;
import ca.uqac.lif.xml.XmlElement;
import ca.uqac.lif.xml.XPathExpression.XPathParseException;

/**
 * Function that converts a string into an XML element
 */
public class XPathFunction extends UnaryFunction<XmlElement,Collection<XmlElement>> 
{
	/**
	 * The XPath expression this function evaluates
	 */
	private final XPathExpression m_expression;
	
	@SuppressWarnings("unchecked")
	public XPathFunction(String exp)
	{
		super(XmlElement.class, (Class<Collection<XmlElement>>) (Object) Collection.class);
		m_expression = parseExpression(exp);
	}
	
	/**
	 * Creates a new XPath function
	 * @param exp The XPath expression to evaluate
	 */
	@SuppressWarnings("unchecked")
	public XPathFunction(XPathExpression exp)
	{
		/* The double cast below is a bit of trickery to pass the
		 * runtime type of the collection. It was found here:
		 * http://stackoverflow.com/a/30754982
		 */
		super(XmlElement.class, (Class<Collection<XmlElement>>) (Object) Collection.class);
		m_expression = exp;
	}
	
	@Override
	public /*@NonNull*/ Collection<XmlElement> getValue(/*NonNull*/ XmlElement x)
	{
		return m_expression.evaluate(x);
	}
	
	/**
	 * Parses an XPath expression from a string
	 * @param s The string to parse
	 * @return An expression, or <code>null</code> if the parsing failed
	 */
	public static XPathExpression parseExpression(String s)
	{
		XPathExpression out =  null;
		try 
		{
			out = XPathExpression.parse(s);
		} 
		catch (XPathParseException e) 
		{
			// Silently fail
		}
		return out;
	}
	
	@Override
	public String toString()
	{
		return m_expression.toString();
	}
	
	@Override
	public XPathFunction clone(Context context)
	{
		XPathExpression exp = XPathFunction.evaluatePlaceholders(m_expression, context);
		XPathFunction out = new XPathFunction(exp);
		return out;
	}
	
	/**
	 * Replaces all occurrences of placeholders in an XPath expression by
	 * concrete values fetched from some context. Placeholders are
	 * currently only supported in binary predicates, and are identified
	 * by a "$" symbol followed by some name
	 * @param expression The original expression
	 * @param context The context
	 * @return The new expression where placeholders have been replaced
	 */
	protected static XPathExpression evaluatePlaceholders(XPathExpression expression, Context context)
	{
		if (context == null)
		{
			return expression;
		}
		List<Segment> segments = expression.getSegments();
		List<Segment> new_segments = new LinkedList<Segment>();
		for (Segment seg : segments)
		{
			if (seg instanceof TextSegment)
			{
				new_segments.add(seg);
				continue;
			}
			String seg_name = seg.getElementName();
			List<Predicate> new_predicates = new LinkedList<Predicate>();
			Collection<Predicate> preds = seg.getPredicates();
			if (preds != null)
			{
				for (Predicate pred : seg.getPredicates())
				{
					if (pred instanceof Equality)
					{
						Equality eq = (Equality) pred;
						String right = eq.getRight();
						String new_right = right;
						if (right.startsWith("$"))
						{
							// This is a placeholder
							String placeholder_name = right.substring(1);
							if (context.containsKey(placeholder_name))
							{
								Object value = context.get(placeholder_name);
								if (value instanceof String)
								{
									new_right = (String) value;
								}
								else if (value instanceof TextElement)
								{
									new_right = ((TextElement) value).getText();
								}
							}
						}
						Equality new_eq = new Equality(eq.getLeft(), new_right);
						new_predicates.add(new_eq);
					}
					else
					{
						new_predicates.add(pred);
					}
				}			
			}
			Segment new_seg = new Segment(seg_name, new_predicates);
			new_segments.add(new_seg);	
		}
		XPathExpression exp = new XPathExpression(new_segments);
		return exp;
	}
}