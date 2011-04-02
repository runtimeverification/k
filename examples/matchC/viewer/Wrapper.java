class Wrapper
{

  public static final int DEFAULT_WIDTH = 80;
  public static final int DEFAULT_LEFT_MARGIN = 0;
  public static final int DEFAULT_RIGHT_MARGIN = 0;

  int width;
  int leftMargin;
  int rightMargin;
  StringBuilder buffer;
  int cursor;
  StringBuilder pendingBuffer;
  int pendingCursor;
  boolean isPending;
  boolean isBackquote;
  boolean isBackslash;
  boolean isString;
  boolean isEscape;


  public Wrapper()
  {
    this(DEFAULT_WIDTH, DEFAULT_LEFT_MARGIN, DEFAULT_RIGHT_MARGIN);
  }

  public Wrapper(int width)
  {
    this(width, DEFAULT_LEFT_MARGIN, DEFAULT_RIGHT_MARGIN);
  }

  public Wrapper(int width, int leftMargin, int rightMargin)
  {
    assert width > 0;
    assert leftMargin > 0;
    assert rightMargin > 0;
    assert width - leftMargin - rightMargin > 0;

    this.width = width;
    this.leftMargin = leftMargin;
    this.rightMargin = rightMargin;
    buffer = new StringBuilder(1024 * 1024);
    cursor = 0;
    pendingBuffer = new StringBuilder(width);
    pendingCursor = 0;
    isPending = false;
    isBackquote = false;
    isBackslash = false;
    isString = false;
    isEscape = false;

    for (int i = 0; i < leftMargin; ++i)
      buffer.append(' ');
    cursor = leftMargin;
  }


  public int getWidth()
  {
    return width;
  }

  public void setWidth(int width)
  {
    this.width = width;
  }

  public int getLeftMargin()
  {
    return leftMargin;
  }

  public void setLeftMargin(int leftMargin)
  {
    this.leftMargin = leftMargin;
  }

  public int getRightMargin()
  {
    return rightMargin;
  }

  public void setRightMargin(int rightMargin)
  {
    this.rightMargin = rightMargin;
  }


  public void clean()
  {
    buffer.setLength(0);
    cursor = 0;
    pendingBuffer.setLength(0);
    pendingCursor = 0;
    isPending = false;
    isBackquote = false;
    isBackslash = false;
    isString = false;
    isEscape = false;

    for (int i = 0; i < leftMargin; ++i)
      buffer.append(' ');
    cursor = leftMargin;
  }

  public String toString()
  {
    return buffer.toString() + pendingBuffer.toString();
  }


  public Wrapper append(String str)
  {
    for (int i = 0; i < str.length(); ++i)
      append(str.charAt(i));

    return this;
  }

  public Wrapper append(char ch)
  {
    if (ch == '\033')
      isEscape = true;
    if (isEscape)
    {
      if (ch == 'm')
        isEscape = false;

      appendNonPrintable(ch);
      return this;
    }

    if (ch == '\n')
    {
      flushPending();
      appendNewline();
      return this;
    }

    if (ch == '"' && !isBackslash)
      isString = !isString;

    if (cursor + pendingCursor >= width - rightMargin)
    {
      appendNewline();
      flushPending();
    }

    appendPrintable(ch);
    
    switch (ch)
    {
      case ' ':
        if (!isString)
        {
          flushPending();
          isPending = true;
        }
        break;
      case ',':
      case '(':
      case '[':
      case '{':
      case ')':
      case ']':
      case '}':
        if (!isString && !isBackquote)
        {
          flushPending();
          isPending = true;
        }
        break;
    }

    isBackquote = (ch == '`');
    isBackslash = isString && !isBackslash && (ch == '\\');

    return this;
  }

  void appendPrintable(char ch)
  {
    if (isPending)
    {
      ++pendingCursor;
      pendingBuffer.append(ch);
    }
    else
    {
      ++cursor;
      buffer.append(ch);
    }
  }

  private void appendNonPrintable(char ch)
  {
    if (isPending)
      pendingBuffer.append(ch);
    else
      buffer.append(ch);
  }

  private void appendNewline()
  {
    //for (int i = 0; i < width - cursor; ++i)
    //  buffer.append(' ');
    buffer.append('\n');
    for (int i = 0; i < leftMargin; ++i)
      buffer.append(' ');
    cursor = leftMargin;
  }

  private void flushPending()
  {
    if (isPending)
    {
      buffer.append(pendingBuffer);
      cursor += pendingCursor;
      pendingBuffer.setLength(0);
      pendingCursor = 0;
      isPending = false;
    }
  }


/*
  public static void main(String[] args)
  {
    Wrapper wrapper = new Wrapper(4, 2, 1);
    wrapper.append("1+2+3+(45\n-23)");
    System.out.println(wrapper);
  }
*/

}

