// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.kframework.kil.ASTNode;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Module;
import org.kframework.kil.Require;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.kompile.KompileOptions.Backend;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.basic.Basic;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

public class BasicParser {
    private List<DefinitionItem> moduleItems;
    private Map<String, Module> modulesMap;
    private List<String> filePaths;
    private File mainFile;
    private String mainModule;
    private boolean autoinclude;
    private static final String missingFileMsg = "Could not find 'required' file: ";

    private KompileOptions kompileOptions;
    private GlobalOptions globalOptions;

    public BasicParser(boolean autoinclude, KompileOptions kompileOptions) {
        this.autoinclude = autoinclude;
        this.kompileOptions = kompileOptions;
        this.globalOptions = kompileOptions.global;
    }

    /**
     * Given a file, this method parses it and creates a list of modules from all of the included files.
     */
    public void slurp(String fileName, Context context) {
        moduleItems = new ArrayList<DefinitionItem>();
        modulesMap = new HashMap<String, Module>();
        filePaths = new ArrayList<String>();

        try {
            // parse first the file given at console for fast failure in case of error
            File file = new File(fileName);
            if (!file.exists())
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, missingFileMsg + fileName + " given at console.", "", ""));

            slurp2(file, context);

            if (autoinclude) {
                // parse the autoinclude.k file but remember what I parsed to give the correct order at the end
                List<DefinitionItem> tempmi = moduleItems;
                moduleItems = new ArrayList<DefinitionItem>();

                if (context.kompileOptions.backend.java())
                    file = buildCanonicalPath("autoinclude-java.k", new File(fileName));
                else
                    file = buildCanonicalPath("autoinclude.k", new File(fileName));
                if (file == null)
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
                            missingFileMsg + fileName + " autoimported for every definition ", fileName, ""));

                slurp2(file, context);
                moduleItems.addAll(tempmi);
            }

            setMainFile(file);
            context.finalizeRequirements();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private File buildCanonicalPath(String fileName, File parentFile) throws IOException {
        File file = new File(parentFile.getCanonicalFile().getParent() + "/" + fileName);
        if (file.exists())
            return file;
        file = new File(KPaths.getKBase(false) + "/include/" + fileName);
        if (file.exists())
            return file;

        return null;
    }

    private void slurp2(File file, Context context) throws IOException {
        String canonicalPath = file.getCanonicalPath();
        if (!filePaths.contains(canonicalPath)) {
            filePaths.add(canonicalPath);

            if (globalOptions.verbose)
                System.out.println("Including file: " + file.getAbsolutePath());
            List<DefinitionItem> defItemList = Basic.parse(file.getAbsolutePath(), FileUtil.getFileContent(file.getAbsolutePath()), context);

            // go through every required file
            for (ASTNode di : defItemList) {
                if (di instanceof Require) {
                    Require req = (Require) di;

                    File newFile = buildCanonicalPath(req.getValue(), file);

                    if (newFile == null)
                        GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, missingFileMsg + req.getValue(), req.getFilename(), req
                                .getLocation()));

                    slurp2(newFile, context);
                    context.addFileRequirement(newFile.getCanonicalPath(), file.getCanonicalPath());
                }
            }

            boolean predefined = file.getCanonicalPath().startsWith(KPaths.getKBase(false) + File.separator + "include");
            if (!predefined)
                context.addFileRequirement(buildCanonicalPath("autoinclude.k", file).getCanonicalPath(), file.getCanonicalPath());

            // add the modules to the modules list and to the map for easy access
            for (DefinitionItem di : defItemList) {
                if (predefined)
                    di.setPredefined(true);

                this.moduleItems.add(di);
                if (di instanceof Module) {
                    Module m = (Module) di;
                    Module previous = this.modulesMap.put(m.getName(), m);
                    if (previous != null) {
                        String msg = "Found two modules with the same name: " + m.getName();
                        GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                                KExceptionGroup.CRITICAL, msg, m.getFilename(), m.getLocation()));
                    }
                }
            }
        }
    }

    public void setMainFile(File mainFile) {
        this.mainFile = mainFile;
    }

    public File getMainFile() {
        return mainFile;
    }

    public void setMainModule(String mainModule) {
        this.mainModule = mainModule;
    }

    public String getMainModule() {
        return mainModule;
    }

    public List<DefinitionItem> getModuleItems() {
        return moduleItems;
    }

    public void setModuleItems(List<DefinitionItem> moduleItems) {
        this.moduleItems = moduleItems;
    }

    public Map<String, Module> getModulesMap() {
        return modulesMap;
    }

    public void setModulesMap(Map<String, Module> modulesMap) {
        this.modulesMap = modulesMap;
    }
}
