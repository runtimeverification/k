// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

/**
 * Thrown from a hook to indicate that the hook represents a function which cannot evaluate
 * during kompile, and therefore evaluation should be immediately terminated.
 * @author dwightguth
 *
 */
public class ImpureFunctionException extends RuntimeException {}
