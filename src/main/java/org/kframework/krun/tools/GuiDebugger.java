package org.kframework.krun.tools;

import org.kframework.kil.Attributes;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.gui.Controller.RunKRunCommand;
import org.kframework.krun.gui.UIDesign.MainWindow;
import org.kframework.transformation.Transformation;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.Main;

import com.google.inject.Inject;

public class GuiDebugger implements Transformation<Void, Void> {

    private final Debugger debugger;
    private final Context context;
    private final KExceptionManager kem;
    private final Term initialConfiguration;

    @Inject
    GuiDebugger(
            @Main Debugger debugger,
            @Main Context context,
            KExceptionManager kem,
            @Main Term initialConfiguration) {
        this.debugger = debugger;
        this.context = context;
        this.kem = kem;
        this.initialConfiguration = initialConfiguration;
    }

    @Override
    public Void run(Void v, Attributes a) {
        a.add(Context.class, context);
        try {
            System.setProperty("java.awt.headless", "false");
            RunKRunCommand cmd = new RunKRunCommand(initialConfiguration, debugger, context);
            MainWindow window = new MainWindow(cmd);
            synchronized(window.lock) {
                while (true) {
                    try {
                        window.lock.wait();
                        return null;
                    } catch (InterruptedException e) {
                        //keep waiting
                    }
                }
            }
        } catch (KRunExecutionException e) {
            kem.registerCriticalError(e.getMessage(), e);
            throw new AssertionError("unreachable");
        }
    }

    @Override
    public String getName() {
        return "--debugger-gui";
    }

}
