package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import org.key_project.logic.Name;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import java.util.HashMap;
import java.util.Map;

import static de.uka.ilkd.key.ldt.HeapLDT.MHEAP_PREFIX;

/**
 * This LDT is primarily concerned with access to a constant encoding for every method in all namespaces. These
 * constant encodings are needed for tracing events.
 */
public class MethodLDT extends LDT {
    public static final Name NAME = new Name("MethodId");

    private static final String METHOD_DELIM = "#";
    private static final String PARAMS_DELIM = "$";
    private static final String PARAM_DELIM = "_";
    private static Map<JFunction, LocationVariable> methodNameConstants = new HashMap<>();

    public MethodLDT(Services services) {
        super(NAME, services);
    }

    public void reloadConstants(Services services) {
        for (JFunction methodConstant : methodNameConstants.keySet()) {
            if (services.getNamespaces().functions().contains(methodConstant)) {
                continue;
            }
            services.getNamespaces().functions().add(methodConstant);
            services.getNamespaces().programVariables().addSafely(methodNameConstants.get(methodConstant));
        }
    }

    /**
     * Constructs a JFunction for a given MethodDeclaration methDecl through custom encoding.
     * Since we want a different MethodId for every overload, we need to encode the parameters too.
     * Encoding: . -> _ | :: -> # | $param1_param2_...
     * E.g., given the method java.lang.Object::equals  Name("java_lang_Object#equals$java_lang_Object")
     *
     * @param containerType The container containing mappings from java types to KeY logic sorts.
     * @param methDecl      The MethodDeclaration to encode.
     * @return The constructed JFunction for the MethodDeclaration.
     */
    public boolean addMethodSafely(Services services, KeYJavaType containerType, MethodDeclaration methDecl) {
        if (containerType == null) {
            return false;
        }
        if (methDecl == null) {
            return false;
        }
        final String fullTypeName = containerType.getFullName();
        final String methodName = methDecl.getName();
        final Name newMethodId;
        newMethodId = constructMethodIdentifier(fullTypeName, methodName, constructParams(methDecl.getParameters()));
        final JFunction method = new JFunction(newMethodId, targetSort(), true, false);
        if (methodConstantExists(newMethodId)) {
            return false;
        }
        services.getNamespaces().functions().add(method);
        // We add one heap per method identifier to the program variables. These heaps are unique because every method identifier is unique.
        if(!addMethodHeapToPVs(services, method)) {
            return false;
        }
        var mHeap = getMethodHeap(services, method);
        services.getTypeConverter().getHeapLDT().addMethodHeap(mHeap);
        methodNameConstants.put(method, mHeap);
        return true;
    }

    private LocationVariable getMethodHeap(Services services, JFunction method) {
        return (LocationVariable)services.getNamespaces().programVariables().lookup(MHEAP_PREFIX + method.name());
    }

    private boolean addMethodHeapToPVs(Services services, JFunction method) {
        if (method == null) {
            return false;
        }
        final ProgramElementName heapName =
                new ProgramElementName(MHEAP_PREFIX + method.name());
        final LocationVariable heapVar = new LocationVariable(heapName,
                services.getNamespaces().sorts().lookup("Heap"));
        services.getNamespaces().programVariables().addSafely(heapVar);
        return true;
    }

    /**
     * Gets the corresponding JFunction for a method that is contained in the namespace.
     *
     * @param fnType Fully qualified fn type.
     * @param mnInst The method name.
     * @param params An array of parameter types.
     * @return The JFunction that is requested.
     */
    public JFunction getMethodNameConstant(String fnType, MethodName mnInst, ImmutableArray<String> params) {
        final var methodNameToFind = constructMethodIdentifier(fnType, mnInst.toString(),
                constructParams(params));
        final JFunction methodNameConstant;
        if ((methodNameConstant = getRegisteredMethodIdentifier(methodNameToFind)) == null) {
            throw new RuntimeException(MethodLDT.class + ": MethodName constant '"
                    + methodNameToFind + "' does not exist.");
        }
        var mcsAsList = methodNameConstants.keySet().stream().toList();
        return mcsAsList.get(mcsAsList.indexOf(methodNameConstant));
    }

    private boolean methodConstantExists(Name candidate) {
        for (var methodConstant : methodNameConstants.keySet()) {
            if (methodConstant.name().equals(candidate)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Constructs the MethodId from the given parts.
     * Format: {@code fullTypeName}{@value METHOD_DELIM}{@code methodName}{@value PARAMS_DELIM}{@code paramTypes}
     *
     * @param fullTypeName The type name of the reference.
     * @param methodName   The method name.
     * @param paramTypes   The parameter type list.
     * @return The constructed MethodId.
     */
    private Name constructMethodIdentifier(String fullTypeName, String methodName, String paramTypes) {
        final StringBuffer signature = new StringBuffer();
        signature.append(fullTypeName.replaceAll("\\.", "_"))
                .append(METHOD_DELIM)
                .append(methodName)
                .append(paramTypes.isEmpty() ? "" : PARAMS_DELIM)
                .append(paramTypes.replaceAll("\\.", "_"));
        return new Name(signature.toString());
    }

    /**
     * Retrieve a MethodName constant by its Name.
     *
     * @param methodNameCandidateName The name of the MethodName constant.
     * @return The MethodName constant for {@code methodNameCandidateName} or {@code null} if there was no constant
     * with that
     * name.
     */
     public JFunction getRegisteredMethodIdentifier(Name methodNameCandidateName) {
        var potentialMatch =
                methodNameConstants.keySet().stream().filter(mnc -> mnc.name().equals(methodNameCandidateName)).findFirst();
        return potentialMatch.orElse(null);
    }

    /**
     * Constructs the parameter encoding for a method.
     * Format: param1{@value PARAM_DELIM}param2{@value PARAM_DELIM}...paramN
     *
     * @param params The parameter types.
     * @param <T>    The encoding algorithm depends on how the parameter types are passed to this method.
     * @return The parameter encoding.
     */
    private <T> String constructParams(ImmutableArray<T> params) {
        StringBuilder paramStrBuilder = new StringBuilder();
        for (var param : params) {
            if (param instanceof ParameterDeclaration) {
                paramStrBuilder.append(((ParameterDeclaration) param).getVariableSpecification()
                        .getType().getFullName()).append(PARAM_DELIM);
            } else if (param instanceof String) {
                paramStrBuilder.append((String) param).append(PARAM_DELIM);
            } else {
                throw new RuntimeException(MethodLDT.class + ": Unknown type '" + param.getClass() + "'.");
            }
        }
        if (params.size() > 0) {
            paramStrBuilder.delete(paramStrBuilder.length() - PARAM_DELIM.length(), paramStrBuilder.length());
        }
        return paramStrBuilder.toString();
    }

    @Override
    public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right, Services services, ExecutionContext ec) {
        return false;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, TermServices services, ExecutionContext ec) {
        return false;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        return null;
    }

    @Override
    public JFunction getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        return null;
    }

    @Override
    public boolean hasLiteralFunction(JFunction f) {
        return false;
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        return null;
    }

    @Override
    public Type getType(Term t) {
        return null;
    }
}
