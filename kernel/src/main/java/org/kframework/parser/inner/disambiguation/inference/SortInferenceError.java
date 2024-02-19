// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.parser.inner.disambiguation.inference;

import java.util.Optional;
import org.kframework.attributes.HasLocation;
import org.kframework.kore.Sort;
import org.kframework.parser.ProductionReference;
import org.kframework.utils.errorsystem.KEMException;

/**
 * The parent class of all errors thrown by SortInferencer. We use our own exceptions here rather
 * than KEMException because a SortInferenceError may not indicate an actual error by the user,
 * e.g., it may be thrown for a type error in one branch of an Ambiguity to indicate that it should
 * be pruned.
 */
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

/** An error indicating that we could not compute some type join / meet. */
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

/** An error indicating that a sub-typing constraint is invalid. */
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

/** An error indicating that some type variable cannot be monomorphized as an actual K sort. */
final class MonomorphizationError extends SortInferenceError {
  // TODO: Produce better error messages!
  //
  // Type variables can originate from three places:
  // - variables
  // - sort parameters
  // - as a generalization of the sort of a production
  //
  // For the first two cases, we could provide nicer error messages by pointing to the
  // location where the type variable originated, reporting all bounds on the
  // variable, and stating that they cannot be satisfied.
  //
  // However, it's unclear how to easily explain errors in the third case.
  //
  // Additionally, there are cases where two type variables may be individually but
  // not mutually monomorphized, so its not clear how to report the root cause.
  public MonomorphizationError(HasLocation loc) {
    super(
        "Term is not well-sorted due to monomorphization failure. Add sort annotations to "
            + "produce a better error message.",
        loc);
  }
}
