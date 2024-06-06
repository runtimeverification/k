// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework;

import java.io.Serializable;
import java.util.function.Supplier;

@FunctionalInterface
public interface SerializableSupplier<T> extends Supplier<T>, Serializable {}
