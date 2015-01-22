// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package Concrete;

import org.eclipse.imp.preferences.PreferencesService;
import org.eclipse.imp.runtime.PluginBase;
import org.osgi.framework.BundleContext;

public class Activator extends PluginBase
{
  public static final String kPluginID = "Concrete";

  public static final String kLanguageName = "Concrete";

  protected static Activator sPlugin;

  public static Activator getInstance()
  {
    if(sPlugin == null)
      return new Activator();
    return sPlugin;
  }

  public Activator ()
  {
    super();
    sPlugin = this;
  }

  @Override public void start(BundleContext context) throws Exception
  {
    super.start(context);
  }

  @Override public String getID()
  {
    return kPluginID;
  }

  @Override public String getLanguageID()
  {
    return kLanguageName;
  }

  protected static PreferencesService preferencesService = null;
}