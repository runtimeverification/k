// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kore;

import static org.kframework.kore.KORE.*;

import java.util.function.UnaryOperator;
import org.kframework.attributes.Att;

public class AddAtt extends TransformK {
  private final UnaryOperator<Att> f;

  public AddAtt(UnaryOperator<Att> f) {
    this.f = f;
  }

  @Override
  public K apply(KApply kapp) {
    return KApply(kapp.klabel(), kapp.klist(), f.apply(kapp.att()));
  }

  @Override
  public K apply(KRewrite rew) {
    return KRewrite(rew.left(), rew.right(), f.apply(rew.att()));
  }

  @Override
  public K apply(KToken tok) {
    return KToken(tok.s(), tok.sort(), f.apply(tok.att()));
  }

  @Override
  public K apply(KVariable var) {
    return KVariable(var.name(), f.apply(var.att()));
  }

  @Override
  public K apply(KSequence kseq) {
    return KSequence(kseq.items(), f.apply(kseq.att()));
  }

  @Override
  public K apply(InjectedKLabel lbl) {
    return InjectedKLabel(lbl.klabel(), f.apply(lbl.att()));
  }

  @Override
  public K apply(KAs kas) {
    return KAs(kas.pattern(), kas.alias(), f.apply(kas.att()));
  }
}
