package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.ImmutableArray;

import java.util.ArrayList;

/**
 * Converts a method call into a {@link MethodName} and instantiates {@code newMethodName} with it.
 */
public class GetMethodNameCondition implements VariableCondition {
    private final SchemaVariable newMethodName;
    private final SchemaVariable objName;
    private final SchemaVariable methodName;
    private final SchemaVariable params;

    public GetMethodNameCondition(SchemaVariable newMethodName, SchemaVariable objName, SchemaVariable methodName,
                                  SchemaVariable params) {
        this.newMethodName = newMethodName;
        this.objName = objName;
        this.methodName = methodName;
        this.params = params;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
                                 MatchConditions mc,
                                 Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        var ec = svInst.getContextInstantiation().activeStatementContext();
        var methodLDT = services.getTypeConverter().getMethodLDT();
        ReferencePrefix fnInst = (ReferencePrefix) svInst.getInstantiation(this.objName);
        MethodName mnInst = (MethodName) svInst.getInstantiation(this.methodName);
        ImmutableArray<ProgramElement> paramsInst =
                (ImmutableArray<ProgramElement>) svInst.getInstantiation(this.params);
        if (mnInst == null || paramsInst == null || ec == null) {
            return mc;
        }
        String fieldType = null;
        if (fnInst == null || fnInst instanceof ThisReference || fnInst instanceof SuperReference) {
            fieldType = services.getTypeConverter().getKeYJavaType((Expression) ec.getRuntimeInstance()).getFullName();
        } else {
            fieldType = services.getTypeConverter().getKeYJavaType((Expression) fnInst).getFullName();
        }
        final var paramsArr = toExpArray(paramsInst);
        var paramTypes = new ArrayList<String>();
        for (Expression p : paramsArr) {
            paramTypes.add(services.getTypeConverter().getKeYJavaType(p).getFullName());
        }
        final JFunction methodNameConst = methodLDT.getMethodNameConstant(fieldType, mnInst,
                new ImmutableArray<>(paramTypes));
        var methodTerm = services.getTermBuilder().func(methodNameConst);
        var ret = svInst.add(this.newMethodName, methodTerm, services);
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