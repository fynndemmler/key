package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.ImmutableArray;

import java.util.ArrayList;

public class GetObjectCondition implements VariableCondition {
    public final static String NAME = "\\newMethodName";

    private final SchemaVariable objName;
    private final SchemaVariable objPlaceholder;

    public GetObjectCondition(SchemaVariable objName, SchemaVariable objPlaceholder) {
        this.objName = objName;
        this.objPlaceholder = objPlaceholder;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
                                 MatchConditions mc,
                                 Services services) {
        SVInstantiations svInst = mc.getInstantiations();
        var fnInst = svInst.getInstantiation(this.objName);
        if (fnInst == null) {
            // TODO: Throw err
            return null;
        }
        // var fnFunc = (JFunction) fnInst;
        //var pv = services.getNamespaces().programVariables().lookup(fnInst.toString());
        //pv.getKeYJavaType()
        JFunction fnFunc = services.getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable) fnInst,
                services);
        //final var fieldType = services.getTypeConverter().getKeYJavaType((Expression) fnInst).getFullName();
        var ini = services.getTermBuilder().func(fnFunc);
        var ret = svInst.add(this.objPlaceholder, ini, services);
        return mc.setInstantiations(ret);
    }
}
