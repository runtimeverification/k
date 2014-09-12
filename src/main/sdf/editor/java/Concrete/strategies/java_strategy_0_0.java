// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package Concrete.strategies;

import org.spoofax.interpreter.terms.IStrategoTerm;
import org.spoofax.interpreter.terms.ITermFactory;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

/**
 * Example Java strategy implementation.
 *
 * This strategy can be used by editor services and can be called
 * in Stratego modules by declaring it as an external strategy
 * as follows:
 *
 * <code>
 *  external java-strategy(|)
 * </code>
 *
 * @see InteropRegisterer  This class registers java_strategy_0_0 for use.
 */
public class java_strategy_0_0 extends Strategy {

  public static java_strategy_0_0 instance = new java_strategy_0_0();

  @Override
  public IStrategoTerm invoke(Context context, IStrategoTerm current) {
    context.getIOAgent().printError("Input for java-strategy: " + current);
    ITermFactory factory = context.getFactory();
    return factory.makeString("Regards from java-strategy");
  }

}
