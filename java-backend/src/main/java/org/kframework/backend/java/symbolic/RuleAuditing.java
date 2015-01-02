// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Rule;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;

import com.google.common.collect.Iterables;

public class RuleAuditing {

    private static class AuditState {
        Rule auditingRule;
        boolean isSuccess = false;
        boolean isFailure = false;
        boolean isBegun = false;

        AuditState(Rule rule) {
            this.auditingRule = rule;
        }

        AuditState() {}
    }

    private static ThreadLocal<AuditState> auditState = new ThreadLocal<>();

    public static Rule getAuditingRule() {
        if (!isAudit()) return null;
        return auditState.get().auditingRule;
    }

    public static void setAuditingRule(JavaExecutionOptions options, int currentStep, Definition def) {
        List<Rule> matchedRules = new ArrayList<>();
        if (options.auditingStep != null && currentStep == options.auditingStep) {
            if (options.auditingFile == null && options.auditingLine == null) {
                auditState.set(new AuditState());
                beginAudit();
                System.err.println("Auditing step " + currentStep + "...");
                return;
            }
            for (Rule rule : Iterables.concat(def.rules(), def.functionRules().values())) {
                if (rule.getSource() == null || rule.getLocation() == null) {
                    continue;
                }
                if (rule.getSource().toString().contains(options.auditingFile)
                        && rule.getLocation().lineStart == options.auditingLine) {
                    matchedRules.add(rule);
                }
            }
            if (matchedRules.size() == 0) {
                throw KExceptionManager.criticalError("Could not find rule for auditing at line "
                        + options.auditingLine + " of file matching " + options.auditingFile);
            } else if (matchedRules.size() > 1) {
                System.err.println("Found multiple matches for rule to audit. Please select one:");
                for (int i = 0; i < matchedRules.size(); i++) {
                    System.err.println(i + ": " + matchedRules.get(i));
                }
                do {
                    System.err.print("> ");
                    System.err.flush();
                    try {
                        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
                        int i = Integer.parseInt(br.readLine());
                        if (i >= 0 && i < matchedRules.size()) {
                            setAuditingRule(matchedRules.get(i));
                            return;
                        }
                    } catch (NumberFormatException e) {
                    } catch (IOException e) {
                        throw KExceptionManager.criticalError("Could not read selection from stdin");
                    }
                } while (true);
            } else {
                setAuditingRule(matchedRules.get(0));
            }
        }
    }

    private static void setAuditingRule(Rule rule) {
        System.err.println("Auditing " + rule + "...");
        auditState.set(new AuditState(rule));
    }

    public static boolean isAudit() {
        return auditState.get() != null;
    }

    public static void clearAuditingRule() {
        if (isAuditBegun()) {
            // auditing all rules, which means we always fail
            throw fail();
        }
        if (isAudit() && !auditState.get().isSuccess && !auditState.get().isFailure) {
            throw KExceptionManager.internalError("Unexpectedly reached the end of an audit step. Please "
                    + "file an issue with a minimal example at https://github.com/kframework/k/issues "
                    + " so that we can add audit instrumentation for your case.");
        }
        auditState.set(null);
    }

    public static void succeed(Rule rule) {
        if (!isAudit()) return;
        if (isAuditBegun() && getAuditingRule() == null) {
            System.err.println("Audit success!");
            return;
        }
        if (getAuditingRule() != rule) return;
        System.err.println("Audit success!");
        auditState.get().isSuccess = true;
    }

    public static boolean isSuccess() {
        return auditState.get().isSuccess;
    }

    public static KEMException fail() {
        return fail("");
    }

    public static KEMException fail(String message) {
        auditState.get().isFailure = true;
        System.err.println(message);
        return KExceptionManager.criticalError("Audit complete");
    }

    public static void beginAudit() {
        if (isAudit())
            auditState.get().isBegun = true;
    }

    public static void endAudit() {
        if (isAudit())
            auditState.get().isBegun = false;
    }

    public static boolean isAuditBegun() {
        return isAudit() && auditState.get().isBegun;
    }
}
