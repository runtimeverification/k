package K3Syntax.strategies;

import java.util.ArrayList;

import org.spoofax.interpreter.terms.IStrategoAppl;
import org.spoofax.interpreter.terms.IStrategoConstructor;
import org.spoofax.interpreter.terms.IStrategoList;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.spoofax.jsglr.client.imploder.IToken;
import org.spoofax.jsglr.client.imploder.ITokenizer;
import org.spoofax.jsglr.client.imploder.ImploderAttachment;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

/**
 * Example Java strategy implementation.
 * 
 * This strategy can be used by editor services and can be called in Stratego modules by declaring it as an external strategy as follows:
 * 
 * <code>
 *  external string-trim-last-one(|)
 * </code>
 * 
 * @see InteropRegisterer This class registers string_trim_last_one_0_0 for use.
 */
public class get_layout_0_0 extends Strategy {

	public static get_layout_0_0 instance = new get_layout_0_0();

	@Override
	public IStrategoTerm invoke(Context context, IStrategoTerm current) {
		// context.getIOAgent().printError("Input for get-layout: " + ls.getCommentsBefore());
		// ITermFactory factory = context.getFactory();
		ITokenizer tkz = ImploderAttachment.getTokenizer(current);
		// context.getIOAgent().printError("tkn: " + tkz.currentToken().getLine());
		// context.getIOAgent().printError("tkn: " + loc1);
		java.util.List<IStrategoTerm> list2 = new ArrayList<IStrategoTerm>();
		for (int i = 0; i < tkz.getTokenCount(); i++) {
			IToken tk = tkz.getTokenAt(i);
			if (tk.getKind() == IToken.TK_LAYOUT && !tk.toString().trim().equals("")) {
				// if (tk.getStartOffset() >= tkz.getStartOffset() && tk.getEndLine() <= tkz.getEndLine())
				// tk.setKind(IToken.TK_STRING);
				// context.getIOAgent().printError("MSG(" + tk.getLine() + "," + tk.getColumn() + "): " + tk.toString());

				IStrategoConstructor constr = context.getFactory().makeConstructor("Comment", 1);
				// IStrategoList ilist = context.getFactory().makeList(context.getFactory().makeString(tk.toString()));
				String loc = "(" + tk.getLine() + "," + tk.getColumn() + "," + tk.getEndLine() + "," + tk.getEndColumn() + ")";
				String str = tk.toString();
				if (str.startsWith("/*")) {
					while (true) {
						if (str.contains("*/"))
							break;
						i++;
						if (!(i < tkz.getTokenCount()))
							break;
						IToken tk2 = tkz.getTokenAt(i);
						if (tk.getKind() != IToken.TK_LAYOUT)
							break;
						str += tk2.toString();
						loc = "(" + tk.getLine() + "," + tk.getColumn() + "," + tk2.getEndLine() + "," + tk2.getEndColumn() + ")";
					}
				}

				IStrategoString content = context.getFactory().makeString(str);
				IStrategoString location = context.getFactory().makeString(loc);
				IStrategoAppl appl = context.getFactory().makeAppl(constr, content, location);
				list2.add(appl);
			}
		}

		// context.getIOAgent().printError("Size: " + list2.size());
		IStrategoList ambl = context.getFactory().makeList(list2);

		return ambl;
	}
}
