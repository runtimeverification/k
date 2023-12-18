// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.kore;

import static org.kframework.kore.KORE.InjectedKLabel;
import static org.kframework.kore.KORE.KApply;
import static org.kframework.kore.KORE.KAs;
import static org.kframework.kore.KORE.KRewrite;
import static org.kframework.kore.KORE.KSequence;
import static org.kframework.kore.KORE.KToken;
import static org.kframework.kore.KORE.KVariable;

import java.util.function.UnaryOperator;
import org.kframework.attributes.Att;

public class AddAttRec extends TransformK {
  private final UnaryOperator<Att> f;

  public AddAttRec(UnaryOperator<Att> f) {
    this.f = f;
  }

  @Override
  public K apply(KApply kapp) {
    return super.apply(KApply(kapp.klabel(), kapp.klist(), f.apply(kapp.att())));
  }

  @Override
  public K apply(KRewrite rew) {
    return super.apply(KRewrite(rew.left(), rew.right(), f.apply(rew.att())));
  }

  @Override
  public K apply(KToken tok) {
    return super.apply(KToken(tok.s(), tok.sort(), f.apply(tok.att())));
  }

  @Override
  public K apply(KVariable var) {
    return super.apply(KVariable(var.name(), f.apply(var.att())));
  }

  @Override
  public K apply(KSequence kseq) {
    return super.apply(KSequence(kseq.items(), f.apply(kseq.att())));
  }

  @Override
  public K apply(InjectedKLabel lbl) {
    return super.apply(InjectedKLabel(lbl.klabel(), f.apply(lbl.att())));
  }

  @Override
  public K apply(KAs kas) {
    return super.apply(KAs(kas.pattern(), kas.alias(), f.apply(kas.att())));
  }
}
