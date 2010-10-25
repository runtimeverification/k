import java.io.IOException;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
public class unwrapBuiltinsMain {
  public static void main (String[] args) {
    try {
      ANTLRInputStream input = new ANTLRInputStream(System.in);
      unwrapBuiltins lexer = new unwrapBuiltins(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      tokens.getTokens();
    }
    catch (IOException e) {}
  }
}

