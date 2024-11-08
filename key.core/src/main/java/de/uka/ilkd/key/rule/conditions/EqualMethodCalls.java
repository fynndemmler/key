package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.logic.SyntaxElement;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import java.util.Map;

public class EqualMethodCalls extends VariableConditionAdapter {
    public final static String NAME = "\\equalMethodCalls";

    private final SchemaVariable caller;
    private final SchemaVariable methodname;
    private final SchemaVariable params;
    private final SchemaVariable methodCall;

    public EqualMethodCalls(SchemaVariable caller, SchemaVariable methodname,
                            SchemaVariable params, SchemaVariable methodCall) {
        this.caller = caller;
        this.methodname = methodname;
        this.params = params;
        this.methodCall = methodCall;
    }

    /**
     * Name of the taclet option. Index to the choice settings
     */
    private final static String TACLET_OPTION_KEY = "equalMethodCalls";
    @SuppressWarnings("unchecked")
    @Override
    public boolean check(SchemaVariable variable, SyntaxElement instCandidate, SVInstantiations instMap, Services services) {
        ReferencePrefix callerRef = (ReferencePrefix) instMap.getInstantiation(caller);
        MethodName mn = (MethodName) instMap.getInstantiation(methodname);
        ImmutableArray<ProgramElement> ar = (ImmutableArray<ProgramElement>) instMap.getInstantiation(params);
        var mcToCompare = (Term)instMap.getInstantiation(methodCall);
        String composedFirstCall = "\"" + callerRef.toString() + "." + mn.toString() + "(";
        for (ProgramElement pe : ar) {
            composedFirstCall += pe.toString() + ", ";
        }
        if (!ar.isEmpty()) {
            composedFirstCall = composedFirstCall.substring(0, composedFirstCall.length() - 2);
        }
        composedFirstCall += ")\"";
        var composedFirstCallSeq = services.getTypeConverter().getCharListLDT().translateLiteral(new StringLiteral(composedFirstCall), services);
        assert composedFirstCallSeq != null;
        return composedFirstCallSeq.equals(mcToCompare);
    }
}
