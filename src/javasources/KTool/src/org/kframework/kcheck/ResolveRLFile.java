// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.parser.ProgramLoader;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

public class ResolveRLFile extends CopyOnWriteTransformer {

    private List<ASTNode> reachabilityRules = new ArrayList<ASTNode>();
    private Term program = null;

    public ResolveRLFile(Context context, String pgmFilePath) {
        super("Parse RL input file", context);

        // resolve reachability rules
        String rlFileContent = null;//FileUtil.getFileContent(GlobalSettings.CHECK);
        context.kompiled = context.dotk.getAbsoluteFile();
        ASTNode rlModule = null;//DefinitionLoader.parseString(rlFileContent,
                //GlobalSettings.CHECK, context);
        RetrieveRRVisitor rrrv = new RetrieveRRVisitor(context);
        rrrv.visitNode(rlModule);
        reachabilityRules = rrrv.getRules();

        // resolve pgm if any
        if (RLBackend.PGM != null) {
            String pgmContent = FileUtil.getFileContent(pgmFilePath);
            //try {
                context.kompiled = context.dotk.getAbsoluteFile();
                //program = (Term) ProgramLoader.loadPgmAst(pgmContent,
                //        GlobalSettings.CHECK, "K", context);
            //} catch (IOException e1) {
            //    e1.printStackTrace();
            //} catch (TransformerException e1) {
            //    e1.printStackTrace();
            //}
        }
    }

    public List<ASTNode> getReachabilityRules() {
        return reachabilityRules;
    }

    public Term getPgm() {
        return program;
    }
}
