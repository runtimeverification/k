package org.kframework.utils.errorsystem;

import org.kframework.main.GlobalOptions;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException.ExceptionType;

import java.util.ArrayList;
import java.util.List;

public class KExceptionManager {
    private final List<KException> exceptions = new ArrayList<KException>();
    
    private GlobalOptions options;
    
    public KExceptionManager(GlobalOptions options) {
        this.options = options;
    }

    public void register(KException exception) {
        exceptions.add(exception);
        if (exception.type == ExceptionType.ERROR)
            print();
    }

    public void print() {
        boolean errors = false;
        for (KException e : exceptions) {
            if (!options.warnings.includesExceptionType(e.type))
                continue;

            if (e.type == ExceptionType.ERROR)
                errors = true;
            System.err.println(StringUtil.splitLines(e.toString()));
        }
        if (errors)
            System.exit(1);
    }
}
