// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.lsp;

import java.util.Objects;
import org.eclipse.lsp4j.Position;

/**
 * KPos a position in a file starting from one. Use this class when converting positions to aviod
 * off by one errors.
 */
public class KPos {

  /** Line position in a document (one-based). */
  private int line;

  /** Character offset on a line in a document (one-based). */
  private int character;

  public KPos(int line, int character) {
    this.line = line;
    this.character = character;
  }

  public KPos(Position pos) {
    this.line = pos.getLine() + 1;
    this.character = pos.getCharacter() + 1;
  }

  public int getLine() {
    return line;
  }

  public void setLine(int line) {
    this.line = line;
  }

  public int getCharacter() {
    return character;
  }

  public void setCharacter(int character) {
    this.character = character;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    KPos kPos = (KPos) o;
    return line == kPos.line && character == kPos.character;
  }

  @Override
  public int hashCode() {
    return Objects.hash(line, character);
  }

  @Override
  public String toString() {
    return "KPos{" + "l:" + line + ", c:" + character + '}';
  }
}
