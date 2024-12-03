package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.rule.conditions.TypeResolver;
import org.key_project.logic.Name;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import java.util.ArrayList;
import java.util.List;

/**
 * This LDT is primarily concerned with access to a constant encoding for every method in all namespaces. These
 * constant encodings are needed for tracing events.
 */
public class MethodLDT extends LDT {
    public static final Name NAME = new Name("MethodName");

    private static final String METHOD_DELIM = "#";
    private static final String PARAMS_DELIM = "$";
    private static final String PARAM_DELIM = "-";
    private static List<JFunction> methodNameConstants = new ArrayList<>();

    public MethodLDT(Services services) {
        super(NAME, services);
    }

    /**
     * Constructs a JFunction for a given MethodDeclaration methDecl through custom encoding.
     * Since we want a different MethodName for every overload, we need to encode the parameters too.
     * Encoding: . -> _ | :: -> # | $param1-param2-...
     * E.g., given the method java.lang.Object::equals  Name("java_lang_Object#equals$java_lang_Object")
     *
     * @param containerType The container containing mappings from java types to KeY logic sorts.
     * @param methDecl      The MethodDeclaration to encode.
     * @return The constructed JFunction for the MethodDeclaration.
     */
    public JFunction addMethodSafely(KeYJavaType containerType, MethodDeclaration methDecl) {
        if (containerType == null) {
            throw new RuntimeException(MethodLDT.class + ": KeYJavaType is null.");
        }
        if (methDecl == null) {
            throw new RuntimeException(MethodLDT.class + ": MethodDeclaration is null.");
        }
        final String fullTypeName = containerType.getFullName();
        final String methodName = methDecl.getName();
        final Name newMethodName;
        newMethodName = constructMethodName(fullTypeName, methodName, constructParams(methDecl.getParameters()));
        final JFunction method = new JFunction(newMethodName, targetSort(), true, false);
        if (methodNameConstants.contains(method)) {
            throw new RuntimeException(MethodLDT.class + ": JFunction '" + method.toString() + "' already exists.");
        }
        methodNameConstants.add(method);
        System.out.println("Added method: " + method.toString());
        return method;
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
        final var methodNameToFind = constructMethodName(fnType, mnInst.toString(),
                constructParams(params));
        final JFunction methodNameConstant;
        if ((methodNameConstant = getRegisteredMethodNameConstant(methodNameToFind)) == null) {
            throw new RuntimeException(MethodLDT.class + ": MethodName constant '"
                    + methodNameToFind + "' does not exist.");
        }
        return methodNameConstants.get(methodNameConstants.indexOf(methodNameConstant));
    }

    /**
     * Constructs the MethodName from the given parts.
     * Format: {@code fullTypeName}{@value METHOD_DELIM}{@code methodName}{@value PARAMS_DELIM}{@code paramTypes}
     *
     * @param fullTypeName The type name of the reference.
     * @param methodName   The method name.
     * @param paramTypes   The parameter type list.
     * @return The constructed MethodName.
     */
    private Name constructMethodName(String fullTypeName, String methodName, String paramTypes) {
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
    private JFunction getRegisteredMethodNameConstant(Name methodNameCandidateName) {
        var potentialMatch =
                methodNameConstants.stream().filter(mnc -> mnc.name().equals(methodNameCandidateName)).findFirst();
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
