// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package Concrete;

import org.strategoxt.imp.runtime.dynamicloading.Descriptor;
import org.strategoxt.imp.runtime.services.MetaFileLanguageValidator;

public class ConcreteValidator extends MetaFileLanguageValidator
{
  @Override public Descriptor getDescriptor()
  {
    return ConcreteParseController.getDescriptor();
  }
}