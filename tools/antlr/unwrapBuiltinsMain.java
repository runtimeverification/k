import java.io.IOException;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
public class unwrapBuiltinsMain {
  public static void main (String[] args) {
    try {
      ANTLRInputStream input = new ANTLRInputStream(System.in);
      unwrapBuiltinsLexer lexer = new unwrapBuiltinsLexer(input);
/*
Token token = lexer.nextToken();
            while(token.getText() != null) {
                System.out.println(token.getText());
                token = lexer.nextToken();
            }
*/
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      unwrapBuiltinsParser parser = new unwrapBuiltinsParser(tokens);
      parser.module();
    }
    catch (IOException e) {}
    catch (RecognitionException e) {}
  }
}
