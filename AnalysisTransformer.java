import java.util.*;
import soot.*;
import soot.jimple.toolkits.callgraph.CallGraph;
import java.util.concurrent.CopyOnWriteArrayList;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.*;
import soot.jimple.*;
import soot.toolkits.scalar.SimpleLiveLocals;
import java.util.regex.*;
import soot.toolkits.scalar.LiveLocals;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ConcurrentMap;
import java.io.FileWriter;
import java.io.BufferedWriter;
import java.io.IOException;
import soot.options.Options;
import soot.jimple.AnyNewExpr;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import java.util.concurrent.CopyOnWriteArraySet;
import soot.jimple.InvokeExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JInstanceFieldRef;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JimpleLocal;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;
import soot.jimple.ParameterRef;
import soot.jimple.internal.JStaticInvokeExpr;

class MethodData {
    private Body body;
    private SootClass className;

    public MethodData(Body body, SootClass className) {
        this.body = body;
        this.className = className;
    }

    public Body getBody() {
        return body;
    }

    public SootClass getClassName() {
        return className;
    }
}

public class AnalysisTransformer extends SceneTransformer {
    static CallGraph cg;
    Map<String,Map<Integer,Map<String,Set<Integer>>>> method_finalGraph=new ConcurrentHashMap<>();
    Map<String,Map<Integer,Integer>> argno_negval_finalmap=new ConcurrentHashMap<>();
    Map<String,Set<Integer>> method_retGraph=new ConcurrentHashMap<>();
    Map<String,Map<Integer,Integer>> method_allObjs=new ConcurrentHashMap<>();
    Map<Integer,String> obj_class=new ConcurrentHashMap<>();
    Map<Unit, MethodData> unit_to_replace=new ConcurrentHashMap<>();
    Map<String, TreeMap<Integer, Integer>> ans = new TreeMap<>(new Comparator<String>() {
        @Override
        public int compare(String o1, String o2) {
            return o1.compareTo(o2);
        }
    });

    @Override
    protected void internalTransform(String arg0, Map<String, String> arg1) {
        cg = Scene.v().getCallGraph();
        SootMethod mainMethod = Scene.v().getMainMethod();
        Integer[] negVal = new Integer[1];
        negVal[0] = -1;
        processCFG(mainMethod, negVal);
        changeClassFile();
        System.out.println("Final statement executed");
    }

    void changeClassFile(){
        List<Unit> unitsToReplace = new CopyOnWriteArrayList<>(unit_to_replace.keySet());
        for(Unit u:unitsToReplace){
            Body body=unit_to_replace.get(u).getBody();
            SootClass targetClass=unit_to_replace.get(u).getClassName();
            InvokeExpr expr = ((Stmt) u).getInvokeExpr();
            VirtualInvokeExpr virtualInvokeExpr = (VirtualInvokeExpr) expr;
            SootMethod targetMethod = virtualInvokeExpr.getMethod();
            List<Type> parameterTypes = new CopyOnWriteArrayList<>(targetMethod.getParameterTypes());
            parameterTypes.add(0,Scene.v().getRefType(targetClass.getName()));
            SootMethod clonedMethod = new SootMethod(targetMethod.getName() + "clone", parameterTypes, targetMethod.getReturnType(), targetMethod.getModifiers() | Modifier.STATIC);
            Body nbody = targetMethod.getActiveBody();
            Body clonedBody = Jimple.v().newBody(clonedMethod);
            clonedMethod.setActiveBody(clonedBody);
            targetClass.addMethod(clonedMethod);
            System.out.println(clonedBody);
            System.out.println(nbody);

            List<Unit> clonedUnits = new CopyOnWriteArrayList<>();
            for (Unit unitt : nbody.getUnits()) {
                Unit clonedUnit = (Unit) unitt.clone();
                if (clonedUnit instanceof IdentityStmt) {
                    IdentityStmt identityStmt = (IdentityStmt) clonedUnit;
                    if (identityStmt.getRightOp() instanceof ThisRef) {
                        ParameterRef param0Ref = Jimple.v().newParameterRef(identityStmt.getLeftOp().getType(), 0);
                        IdentityStmt newIdentityStmt = Jimple.v().newIdentityStmt(identityStmt.getLeftOp(), param0Ref);
                        clonedUnit = newIdentityStmt;
                    }
                }
                clonedUnits.add(clonedUnit);
            }
            clonedBody.getUnits().addAll(clonedUnits);

            List<Local> clonedLocals = new CopyOnWriteArrayList<>();
            for (Local local : nbody.getLocals()) {
                Local clonedLocal = Jimple.v().newLocal(local.getName(), local.getType());
                clonedLocals.add(clonedLocal);
            }
            clonedBody.getLocals().addAll(clonedLocals);
            System.out.println(clonedBody);
            SootMethod staticMethod = clonedMethod;
            StaticInvokeExpr staticInvokeExpr = Jimple.v().newStaticInvokeExpr(staticMethod.makeRef());
            InvokeStmt staticInvokeStmt = Jimple.v().newInvokeStmt(staticInvokeExpr);
            body.getUnits().swapWith((Stmt)u, staticInvokeStmt);
            printClassBodies(targetClass);
        }

    }

    public static void printClassBodies(SootClass sootClass) {
        System.out.println("Class: " + sootClass.getName());
        for (SootMethod method : sootClass.getMethods()) {
            if (!method.isJavaLibraryMethod()) {
                System.out.println("Method: " + method.getSignature());
                if (method.hasActiveBody()) {
                    Body body = method.getActiveBody();
                    System.out.println("Body:");
                    for (Unit unit : body.getUnits()) {
                        System.out.println(unit);
                    }
                    System.out.println();
                } else {
                    System.out.println("No active body for method.");
                }
            }
        }
    }

    protected void processCFG(SootMethod method, Integer negVal[]) {
        if(method.isConstructor()) { return; }
        Body body = method.getActiveBody();
        SootClass clazz = method.getDeclaringClass();
        String result = clazz.getName() + ":" + method.getName();
        
        if(method_finalGraph.containsKey(result)) return;
        method_allObjs.put(result, new HashMap<>());
        Map<Integer,Set<Integer>> line_RetMap=new ConcurrentHashMap<>();
        Map<Unit,Map<String,Set<Integer>>> obj_lineMap= new ConcurrentHashMap<>();
        Map<Unit,Map<String,Set<Integer>>> obj_lineMap2= new ConcurrentHashMap<>();
        Map<String,Set<Integer>> variable_objects_Map=new ConcurrentHashMap<>();
        Set<Integer> vis= new CopyOnWriteArraySet<>();
        Map<Unit,Map<Integer,Map<String,Set<Integer>>>> objgraph=new ConcurrentHashMap<>();
        Map<Unit,Map<Integer,Map<String,Set<Integer>>>> objgraph2=new ConcurrentHashMap<>();
        Queue<Integer> escapingObjs = new ConcurrentLinkedQueue<>();
        Map<Integer,Integer> argno_negval_map=new ConcurrentHashMap<>();
        DirectedGraph<Unit> cfg = new ExceptionalUnitGraph(body);
        
        PatchingChain<Unit> units = body.getUnits();

        for (Unit u : units) {
            obj_lineMap.put(u, new ConcurrentHashMap<>());
            objgraph.put(u, new ConcurrentHashMap<>());
            obj_lineMap2.put(u, new ConcurrentHashMap<>());
            objgraph2.put(u, new ConcurrentHashMap<>());
        }
        
        PointsToAnalysis(cfg,objgraph,obj_lineMap,objgraph2,obj_lineMap2,escapingObjs,vis,negVal,method,
        argno_negval_map,line_RetMap,variable_objects_Map);

        Map<Integer,Map<String,Set<Integer>>> finalGraph=totalMethodGraph(body, cfg,objgraph,obj_lineMap,objgraph2,obj_lineMap2,escapingObjs,vis);
        argno_negval_finalmap.put(result,argno_negval_map);
        if(!method_finalGraph.containsKey(result)) method_finalGraph.put(result, finalGraph);
        Set<Integer> ret=escapeAnalysis(body, cfg,objgraph,obj_lineMap,objgraph2,obj_lineMap2,escapingObjs,vis,finalGraph,line_RetMap,variable_objects_Map);
        method_retGraph.put(result,ret);
    }


    protected int getArgumentNumber(SootMethod method, ParameterRef paramRef) {
        String refString = paramRef.toString();
        
        int argNumber = -1;
        int atIndex = refString.lastIndexOf("@parameter");
        int colonIndex = refString.indexOf(":", atIndex);
        if (atIndex != -1 && colonIndex != -1) {
            String numberString = refString.substring(atIndex + "@parameter".length(), colonIndex);
            try {
                argNumber = Integer.parseInt(numberString.trim());
            } catch (NumberFormatException e) {
                e.printStackTrace();
            }
        }
        return argNumber;
    }

    protected void PointsToAnalysis(DirectedGraph<Unit> cfg, Map<Unit,Map<Integer,Map<String,Set<Integer>>>> objgraphgl, 
    Map<Unit,Map<String,Set<Integer>>> obj_lineMapgl, Map<Unit,Map<Integer,Map<String,Set<Integer>>>> objgraphgl2, 
    Map<Unit,Map<String,Set<Integer>>> obj_lineMapgl2, Queue<Integer> escapingObjs, Set<Integer> vis,
    Integer negVal[], SootMethod method, Map<Integer,Integer> argno_negval_map, Map<Integer,Set<Integer>> line_RetMap,
    Map<String,Set<Integer>> variable_object_Map) {
        Queue<Unit> worklist = new ConcurrentLinkedQueue<>();
        worklist.addAll(cfg.getHeads());
        while (!worklist.isEmpty()) {
            Unit unit = worklist.poll();
            boolean changed = processUnit(negVal,unit,cfg,objgraphgl,obj_lineMapgl,objgraphgl2,
            obj_lineMapgl2,escapingObjs,vis, method, argno_negval_map,line_RetMap,variable_object_Map);
            
            if (changed) {
                List<Unit> successors = cfg.getSuccsOf(unit);
                for (Unit succ : successors) {
                    if (!worklist.contains(succ)) {
                        worklist.add(succ);
                    }
                }
            }
        }
    }

    Map<Integer, Map<String, Set<Integer>>> graphUnion(Map<Integer, Map<String, Set<Integer>>> firstMap,
    Map<Integer, Map<String, Set<Integer>>> secondMap) {
        for (Integer obj : secondMap.keySet()) {
            if (!firstMap.containsKey(obj)) {
                firstMap.put(obj, secondMap.get(obj));
            } else {
                Map<String, Set<Integer>> firstObjFields = firstMap.get(obj);
                Map<String, Set<Integer>> secondObjFields = secondMap.get(obj);
                for (String field : secondObjFields.keySet()) {
                    if (!firstObjFields.containsKey(field)) {
                        firstMap.get(obj).put(field, secondObjFields.get(field));
                    } else {
                        Set<Integer> secondFieldPointedToObjects = secondObjFields.get(field);
                        firstMap.get(obj).get(field).addAll(secondFieldPointedToObjects);
                    }
                }
            }
        }
        return firstMap;
    }

    Map<String,Set<Integer>> lineMapUnion(Map<String,Set<Integer>> firsMap, Map<String,Set<Integer>> 
    secondMap){
        for(String var: secondMap.keySet()){
            if(!firsMap.containsKey(var)){
                firsMap.put(var, secondMap.get(var));
            }
            else{
                firsMap.get(var).addAll(secondMap.get(var));
            }
        }
        return firsMap;
    }

    public static SootMethod getInvokedMethod(JInvokeStmt jInvokeStmt) {
        InvokeExpr invokeExpr = jInvokeStmt.getInvokeExpr();
        SootMethod invokedMethod = invokeExpr.getMethod();
        return invokedMethod;
    }

    boolean change(Map<Integer,Map<String,Set<Integer>>> firstMap, Map<Integer,Map<String,Set<Integer>>>
    secondMap){
        if(firstMap.size()!=secondMap.size()) return true;
        for (Integer obj : secondMap.keySet()) {
            if (!firstMap.containsKey(obj)) {
                return true;
            } else {
                Map<String, Set<Integer>> firstObjFields = firstMap.get(obj);
                Map<String, Set<Integer>> secondObjFields = secondMap.get(obj);
                if(secondObjFields.size()!=firstObjFields.size()) return true;
                for (String field : secondObjFields.keySet()) {
                    if (!firstObjFields.containsKey(field)) {
                        return true;
                    } else {
                        Set<Integer> firstFieldPointedToObjects = firstObjFields.get(field);
                        Set<Integer> secondFieldPointedToObjects = secondObjFields.get(field);
                        if(!firstFieldPointedToObjects.equals(secondFieldPointedToObjects)) return true;
                    }
                }
            }
        }
        return false;
    }

    protected boolean processUnit(Integer negVal[], Unit unit, DirectedGraph<Unit> cfg, Map<Unit,Map<Integer,Map<String,Set<Integer>>>> objgraphgl, 
    Map<Unit,Map<String,Set<Integer>>> obj_lineMapgl, Map<Unit,Map<Integer,Map<String,Set<Integer>>>> objgraphgl2, 
    Map<Unit,Map<String,Set<Integer>>> obj_lineMapgl2, Queue<Integer> escapingObjs, Set<Integer> vis, 
    SootMethod methodd, Map<Integer,Integer> argno_negval_map, Map<Integer,Set<Integer>> line_RetMap,
    Map<String,Set<Integer>> variable_object_Map) {
        Map<Integer,Map<String,Set<Integer>>> objgraph=new ConcurrentHashMap<>();
        Map<String,Set<Integer>> obj_lineMap= new ConcurrentHashMap<>();
        List<Unit> predecessors = cfg.getPredsOf(unit);
        for (Unit pred : predecessors) {
            
            objgraph=graphUnion(objgraph,objgraphgl2.get(pred));
            obj_lineMap=lineMapUnion(obj_lineMap,obj_lineMapgl2.get(pred));
        }
        objgraphgl.put(unit,objgraph);
        obj_lineMapgl.put(unit,obj_lineMap);


        if (unit instanceof JAssignStmt) {
            JAssignStmt stmt = (JAssignStmt) unit;
            
            Value lhs = stmt.getLeftOp();
            Value rhs = stmt.getRightOp();
            if(!variable_object_Map.containsKey(lhs.toString())){
                variable_object_Map.put(lhs.toString(), new HashSet<>());
            }
            if (rhs instanceof JNewExpr) {
                int lineNumber = unit.getJavaSourceStartLineNumber();
                objgraph.put(lineNumber, new HashMap<>());
                if (lhs instanceof JimpleLocal && lhs!=null) {
                    obj_lineMap.put(lhs.toString(), new HashSet<>());
                    obj_lineMap.get(lhs.toString()).add(lineNumber);
                    variable_object_Map.get(lhs.toString()).add(lineNumber);
                }
                Type objectType = ((JNewExpr) rhs).getType();
                obj_class.put(lineNumber, objectType.toString());
            }
            else if(lhs instanceof JimpleLocal && rhs instanceof JimpleLocal && lhs!=null && 
            rhs!=null){
                obj_lineMap.put(lhs.toString(), new HashSet<>());
                if(obj_lineMap.containsKey(rhs.toString())){
                    obj_lineMap.get(lhs.toString()).addAll(obj_lineMap.get(rhs.toString()));
                    variable_object_Map.get(lhs.toString()).addAll(obj_lineMap.get(rhs.toString()));
                }
            }
        }
        else if (unit instanceof JIdentityStmt && ((JIdentityStmt)unit).getRightOp() instanceof ParameterRef){
            JIdentityStmt stmt = (JIdentityStmt) unit;
            Value lhs = stmt.getLeftOp();
            Value rhs = stmt.getRightOp();
            if(!variable_object_Map.containsKey(lhs.toString())){
                variable_object_Map.put(lhs.toString(), new HashSet<>());
            }
            ParameterRef paramRef = (ParameterRef) rhs;
            int argNumber = getArgumentNumber(methodd, paramRef);
            if(rhs instanceof ParameterRef && lhs!=null && rhs!=null) {
                argno_negval_map.put(argNumber,negVal[0]);
                
                
                objgraph.put(negVal[0], new HashMap<>());
                obj_lineMap.put(lhs.toString(), new HashSet<>());
                obj_lineMap.get(lhs.toString()).add(negVal[0]);
                variable_object_Map.get(lhs.toString()).add(negVal[0]);
                objgraphgl2.put(unit,objgraph);
                obj_lineMapgl2.put(unit,obj_lineMap);
                negVal[0]--;
                return true;
            }
        } 
        else{
            objgraphgl2.put(unit,objgraph);
            obj_lineMapgl2.put(unit,obj_lineMap);
            return true;
        }
        Map<Integer,Map<String,Set<Integer>>> outObjgraph=objgraphgl2.get(unit);
        boolean ret=change(objgraph,outObjgraph);
        if(ret){
            objgraphgl2.put(unit,objgraph);
            obj_lineMapgl2.put(unit,obj_lineMap);
        }
        return ret;
    }

    private Map<Integer,Map<String,Set<Integer>>> totalMethodGraph(Body body, DirectedGraph<Unit> cfg, Map<Unit,Map<Integer,Map<String,Set<Integer>>>> objgraphgl, 
    Map<Unit,Map<String,Set<Integer>>> obj_lineMapgl, Map<Unit,Map<Integer,Map<String,Set<Integer>>>> objgraphgl2, 
    Map<Unit,Map<String,Set<Integer>>> obj_lineMapgl2, Queue<Integer> escapingObjs, Set<Integer> vis){
        Map<Integer,Map<String,Set<Integer>>> objgraph=new ConcurrentHashMap<>();
        List<Unit> tails = cfg.getTails();
        for (Unit t : tails) {
            objgraph=graphUnion(objgraph,objgraphgl2.get(t));
        }
        return objgraph;
    }
    
    private Set<Integer> escapeAnalysis(Body body, DirectedGraph<Unit> cfg, Map<Unit,Map<Integer,Map<String,Set<Integer>>>> objgraphgl, 
    Map<Unit,Map<String,Set<Integer>>> obj_lineMapgl, Map<Unit,Map<Integer,Map<String,Set<Integer>>>> objgraphgl2, 
    Map<Unit,Map<String,Set<Integer>>> obj_lineMapgl2, Queue<Integer> escapingObjs, Set<Integer> vis,
    Map<Integer,Map<String,Set<Integer>>> objgraph, Map<Integer,Set<Integer>> line_retMap,
    Map<String,Set<Integer>> variable_object_Map){
        
        PatchingChain<Unit> unitss = body.getUnits();
        for (Unit u : unitss) {
            Map<String,Set<Integer>> var_objs=variable_object_Map;
            if (u instanceof Stmt && ((Stmt) u).containsInvokeExpr()) {
                InvokeExpr expr = ((Stmt) u).getInvokeExpr();
                if (expr instanceof VirtualInvokeExpr) {
                    VirtualInvokeExpr virtualInvokeExpr = (VirtualInvokeExpr) expr;
                    String expression = virtualInvokeExpr.toString();
                    Pattern pattern = Pattern.compile("(r\\d+|\\$r\\d+)");
                    Matcher matcher = pattern.matcher(expression);
                    String variable="#$";
                    while (matcher.find()) {
                        variable = matcher.group();
                    }
                    if (!variable.equals("#$")) {
                        Set<Integer> variable_objects=var_objs.get(variable);
                        Set<String> classess=new HashSet<>();
                        for(Integer i:variable_objects){
                            if(obj_class.containsKey(i))
                            classess.add(obj_class.get(i));
                        }
                        if(classess.size()==1){
                            System.out.println("Monomorphic call site at : "+virtualInvokeExpr);
                            String classname="";
                            for(String s:classess){
                                classname=s;
                            }
                            SootClass targetClass = Scene.v().getSootClass(classname);
                            MethodData methodData = new MethodData(body, targetClass);
                            unit_to_replace.put(u, methodData);
                        }
                    }
                }
            }
        }
        Set<Integer> ret=new HashSet<>();
        return ret;
    }
}

