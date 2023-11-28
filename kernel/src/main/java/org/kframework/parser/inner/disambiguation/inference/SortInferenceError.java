package org.kframework.parser.inner.disambiguation.inference;

import java.util.Optional;
import org.kframework.attributes.HasLocation;
import org.kframework.kore.Sort;
import org.kframework.parser.ProductionReference;
import org.kframework.utils.errorsystem.KEMException;

abstract sealed class SortInferenceError extends Exception {
  private final Optional<HasLocation> loc;

  public SortInferenceError(String message, HasLocation loc) {
    super(message);
    this.loc = Optional.of(loc);
  }

  public KEMException asInnerParseError(HasLocation defaultLoc) {
    return KEMException.innerParserError(getMessage(), loc.orElse(defaultLoc));
  }
}

final class LatticeOpError extends SortInferenceError {
  public LatticeOpError(CompactSort.LatticeOpError err, HasLocation loc, Optional<String> name) {
    super(
        "Sort"
            + name.map(n -> " of " + n + " ").orElse(" ")
            + "inferred as "
            + (err.polarity() ? "least upper bound" : "greatest lower bound")
            + " of "
            + err.sorts()
            + ", but "
            + (err.candidates().isEmpty()
                ? "no such bound exists."
                : ("candidate bounds are " + "incomparable: " + err.candidates() + ".")),
        loc);
  }
}

final class ConstraintError extends SortInferenceError {
  public ConstraintError(Sort lhs, Sort rhs, ProductionReference pr) {
    super(
        "Unexpected sort "
            + lhs
            + " for term parsed as production "
            + pr.production()
            + ". Expected: "
            + rhs,
        pr);
  }
}

final class MonomorphizationError extends SortInferenceError {
  // TODO: Produce better error messages!
  public MonomorphizationError(HasLocation loc) {
    super("Term is not well-sorted due to monomorphization failure.", loc);
  }
}
