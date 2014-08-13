package org.kframework.backend.java.symbolic;

import java.util.HashSet;
import java.util.Set;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.SMTLibTerm;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Z3Exception;

public class KILtoSMTLib extends CopyOnWriteTransformer {

    private final Context context;

    public final Set<Sort> sorts = new HashSet<>();
    public final Set<FuncDecl> funcDecls = new HashSet<>();

    public KILtoSMTLib(Context context) throws Z3Exception {
        this.context = context;
        sorts.add(context.BoolSort());
        sorts.add(context.IntSort());
    }

    public static BoolExpr kilToZ3(Context context, Term t) {
        KILtoSMTLib transformer = null;
        SMTLibTerm smtlib = null;
        try {
            transformer = new KILtoSMTLib(context);
            smtlib = (SMTLibTerm) t.accept(transformer);
            return context.ParseSMTLIB2String(smtlib.expression(), null, null, null, null);
        } catch (Z3Exception e) {
            throw new UnsupportedOperationException(e);
        }
    }

    public Sort[] getSorts() {
        return sorts.toArray(new Sort[sorts.size()]);
    }

    public FuncDecl[] getFuncDecls() {
        return funcDecls.toArray(new FuncDecl[funcDecls.size()]);
    }

    @Override
    public ASTNode transform(BoolToken boolToken) {
        return new SMTLibTerm(Boolean.toString(boolToken.booleanValue()));
    }

    @Override
    public ASTNode transform(IntToken intToken) {
        return new SMTLibTerm(Integer.toString(intToken.intValue()));
    }

    @Override
    public ASTNode transform(BitVector bitVector) {
        return new SMTLibTerm("(_ bv" + bitVector.signedValue().longValue() + " " + bitVector.bitwidth() + ")");
    }

    @Override
    public ASTNode transform(KItem kItem) {
        if (!(kItem.kLabel() instanceof KLabelConstant)) {
            throw new UnsupportedOperationException();
        }
        KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();

        if (!(kItem.kList() instanceof KList)) {
            throw new UnsupportedOperationException();
        }
        KList kList = (KList) kItem.kList();

        if (kList.hasFrame()) {
            throw new UnsupportedOperationException();
        }

        String label;
        Term[] args;
        // TODO(AndreiS): implement a more general mechanic
        if (kLabel.label().equals("'extractMInt")) {
            int beginIndex = ((IntToken) kList.get(1)).intValue();
            int endIndex = ((IntToken) kList.get(2)).intValue() - 1;
            label = "(_ extract " + endIndex + " " + beginIndex + ")";
            args = new Term[] { kList.get(0) };
        } else if (kLabel.label().equals("'concatenateMInt")) {
            label = "concat";
            args = new Term[] { kList.get(1), kList.get(0) };
        } else {
            label = kLabel.smtlib();
            args = kList.getContents().toArray(new Term[kList.size()]);
        }
        StringBuilder sb = new StringBuilder();
        if (args.length == 0) {
            return new SMTLibTerm(label);
        }
        sb.append("(");
        sb.append(label);
        for (Term arg : args) {
            SMTLibTerm smtlib = (SMTLibTerm) arg.accept(this);
            sb.append(" ");
            sb.append(smtlib.expression());
        }
        sb.append(")");
        return new SMTLibTerm(sb.toString());
    }

    @Override
    public ASTNode transform(Variable variable) {
        return valueOf(variable, context);
    }

    public SMTLibTerm valueOf(Variable variable, Context context) {
        try {
            if (variable.sort().equals(BoolToken.SORT)) {
                funcDecls.add(context.MkConstDecl(variable.name(), context.BoolSort()));
                return new SMTLibTerm(variable.name());
            } else if (variable.sort().equals(IntToken.SORT)) {
                funcDecls.add(context.MkConstDecl(variable.name(), context.IntSort()));
                return new SMTLibTerm(variable.name());
            } else if (variable.sort().equals(BitVector.SORT)) {
                Sort sort = context.MkBitVecSort(BitVector.getBitwidth(variable));
                sorts.add(sort);
                funcDecls.add(context.MkConstDecl(variable.name(), sort));
                return new SMTLibTerm(variable.name());
            } else {
                throw new UnsupportedOperationException("cannot translate term to SMTLib format " + variable);
            }
        } catch (Z3Exception e) {
            throw new UnsupportedOperationException(e);
        }
    }
}
