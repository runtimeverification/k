package org.kframework.main;

import java.util.EnumSet;
import java.util.Set;

import org.kframework.kompile.KompileOptions.Backend;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.options.BaseEnumConverter;

import com.beust.jcommander.IStringConverter;
import com.beust.jcommander.Parameter;

public final class GlobalOptions {
    
    public static enum Warnings {
        /**
         * All warnings and errors
         */
        ALL(EnumSet.allOf(ExceptionType.class)), 
        
        /**
         * All warnings and errors except hidden warnings
         */
        NORMAL(EnumSet.complementOf(EnumSet.of(ExceptionType.HIDDENWARNING))), 
        
        /**
         * No warnings, only errors
         */
        NONE(EnumSet.of(ExceptionType.ERROR));
        
        private Warnings(Set<ExceptionType> types) {
            typesIncluded = types;
        }
        private Set<ExceptionType> typesIncluded;
        
        public boolean includesExceptionType(ExceptionType e) {
            return typesIncluded.contains(e);
        }
    }

    public static class WarningsConverter extends BaseEnumConverter<Warnings> implements IStringConverter<Warnings> {

        @Override
        public Warnings convert(String arg0) {
            return convert(Warnings.class, arg0);
        }
    }
    
    /**
     * Temporary bootstrapping method to ensure that all static objects still in existence which depend on this class are properly initialized.
     * 
     * TODO(dwightguth): remove this method when adding a dependency injector
     */
    public void initialize() {
        Stopwatch.instance().init(this);
        GlobalSettings.kem = new KExceptionManager(this);
    }

    @Parameter(names={"--verbose", "-v"}, description="Print verbose output messages")
    public boolean verbose = false;
    
    @Parameter(names={"--warnings", "-w"}, converter=WarningsConverter.class, description="Warning level. Values: [all|normal|none]")
    public Warnings warnings = Warnings.NORMAL;
}
