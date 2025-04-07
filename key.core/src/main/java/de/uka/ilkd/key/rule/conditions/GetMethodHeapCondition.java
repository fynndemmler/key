package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.ImmutableArray;

import java.util.ArrayList;

/**
 * Converts a method call into a {@link MethodName} and instantiates {@code newMethodName} with it.
 */
public class GetMethodHeapCondition implements VariableCondition {
    private final SchemaVariable newHeap;
    private final SchemaVariable mId;

    public GetMethodHeapCondition(SchemaVariable newHeap, SchemaVariable mId) {
        this.newHeap = newHeap;
        this.mId = mId;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
                                 MatchConditions mc,
                                 Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        Term mIdTerm = (Term) svInst.getInstantiation(this.mId);
        var mId = services.getTypeConverter().getMethodLDT().getRegisteredMethodIdentifier(new Name(mIdTerm.toString()));
        if (mId == null) {
            return mc;
        }
        var heapTerm = services.getTypeConverter().getHeapLDT().getMethodHeap(mId);
        if (heapTerm == null) {
            return null;
        }
        var ret = svInst.add(this.newHeap, heapTerm, services);
        return mc.setInstantiations(ret);
    }

    private static ImmutableArray<Expression> toExpArray(
            ImmutableArray<? extends ProgramElement> a) {
        Expression[] result = new Expression[a.size()];
        for (int i = 0; i < a.size(); i++) {
            result[i] = (Expression) a.get(i);
        }
        return new ImmutableArray<>(result);
    }
}
