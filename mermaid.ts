import { Parsed, isProgram, isDefineExp, isAtomicExp, isCompoundExp, parseL4,
        isAppExp, isIfExp, isProcExp, isLetExp, isLetrecExp, isSetExp, isLitExp,
        isPrimOp, CExp, Exp, VarDecl, Binding, isNumExp, isBoolExp, isStrExp,
        isVarRef, isCExp, isVarDecl, Program, isBinding, makeProcExp, makeVarDecl, makeAppExp, makePrimOp, makeNumExp, parseL4Exp } from "./L4-ast";
import { Result, makeOk, isOk, bind } from "../shared/result";
import { Graph, makeNodeDecl, makeCompoundGraph, makeEdge,
        Node, makeEdgeLabel, makeNodeRef, Edge, NodeDecl, Header, makeGraph,
        isCompoundGraph, isNodeDecl, isNodeRef, makeAtomicGraph } from "./mermaid-ast";
import { map, union, flatten, join } from "ramda";
import { isNumber, isString, isBoolean, isArray } from "../shared/type-predicates";
import { isEmptySExp, isSymbolSExp, isCompoundSExp, SExpValue, CompoundSExp } from "./L4-value";
import { parse } from "../shared/parser";

export const mapL4toMermaid = (exp: Parsed): Result<Graph> => 
    isProgram(exp) ? ((expsNode: Node)=> makeOk(makeGraph("TD", makeCompoundGraph(
                                                            union([makeEdge(makeNodeDecl(gen("Program"), `[Program]`), expsNode, makeEdgeLabel("|exps|"))],
                                                                    flatten(map((x:Exp)=>expOrCExp(expsNode.id, x), exp.exps)))))))
                        (makeNodeDecl(gen(`Exps`), `[:]`)) :
    isCompoundExp(exp) || isDefineExp(exp) ? makeOk(makeGraph("TD", makeCompoundGraph(singleExp(makeNodeDecl(gen(exp.tag), printNodeLabel(exp)), exp)))) :
    makeOk(makeGraph("TD", makeAtomicGraph(makeNodeDecl(gen(exp.tag), printNodeLabel(exp)))))

const expOrCExp = (fromId: string, toExp: Exp): Edge[] => 
    isCExp(toExp) ? (((cexpNode:Node):Edge[]=> union([makeEdge(makeNodeRef(fromId), cexpNode)], LastOne(cexpNode.id, toExp)))
                        (makeNodeDecl(gen(toExp.tag), printNodeLabel(toExp)))) : 
    ((vardeclNode: Node, valNode: Node, defineNode:Node)=>
                                        union([makeEdge(makeNodeRef(fromId), defineNode),
                                            makeEdge(makeNodeRef(defineNode.id), vardeclNode, makeEdgeLabel("|var|")),
                                            makeEdge(makeNodeRef(defineNode.id), valNode, makeEdgeLabel("|val|"))],
                                            LastOne(valNode.id ,toExp.val)))
    (makeNodeDecl(gen(toExp.var.tag), printNodeLabel(toExp.var)),
    makeNodeDecl(gen(toExp.val.tag), printNodeLabel(toExp.val)),
    makeNodeDecl(gen(toExp.tag), printNodeLabel(toExp)))

const singleExp = (fromNode: Node, fromExp: Exp): Edge[] =>
    isCExp(fromExp) ? LastOne(fromNode.id, fromExp, fromNode) :
    ((vardeclNode: Node, valNode: Node)=>
                                        union([makeEdge(fromNode, vardeclNode, makeEdgeLabel("|var|")),
                                                makeEdge(makeNodeRef(fromNode.id), valNode, makeEdgeLabel("|val|"))],
                                            LastOne(valNode.id ,fromExp.val)))
    (makeNodeDecl(gen(fromExp.var.tag), printNodeLabel(fromExp.var)),
    makeNodeDecl(gen(fromExp.val.tag), printNodeLabel(fromExp.val)))



const LastOne = (fromId: string, fromExp: CExp, single?: Node): Edge[] => 
    isAtomicExp(fromExp) ? [] :
    isAppExp(fromExp) ? ((ratorNode: Node, randsNode: Node)=> union(union([makeEdge(single || makeNodeRef(fromId), ratorNode, makeEdgeLabel("|rator|")),
                                                                            makeEdge(makeNodeRef(fromId), randsNode, makeEdgeLabel("|rands|"))],
                                                                    LastOne(ratorNode.id, fromExp.rator)),
                                                                    ArrayOfCExp(randsNode.id, fromExp.rands)))
                        (makeNodeDecl(gen(fromExp.rator.tag), printNodeLabel(fromExp.rator)),
                         makeNodeDecl(gen("Rands"), "[:]")) :
    isIfExp(fromExp) ? ((testNode: Node, thenNode: Node, altNode: Node)=>
                                                                    union([makeEdge(single || makeNodeRef(fromId), testNode, makeEdgeLabel("|test|")),
                                                                            makeEdge(makeNodeRef(fromId), thenNode, makeEdgeLabel("|then|")),
                                                                            makeEdge(makeNodeRef(fromId), altNode, makeEdgeLabel("|alt|"))],
                                                                            flatten([LastOne(testNode.id, fromExp.test),
                                                                                    LastOne(thenNode.id, fromExp.then),
                                                                                    LastOne(altNode.id, fromExp.alt)]))) 
                        (makeNodeDecl(gen(fromExp.test.tag), printNodeLabel(fromExp.test)),
                        makeNodeDecl(gen(fromExp.then.tag), printNodeLabel(fromExp.then)),
                        makeNodeDecl(gen(fromExp.alt.tag), printNodeLabel(fromExp.alt))) :
    isProcExp(fromExp) ? ((argsNode: Node, bodyNode: Node)=> union([makeEdge(single || makeNodeRef(fromId), argsNode, makeEdgeLabel("|args|")),
                                                                    makeEdge(makeNodeRef(fromId), bodyNode, makeEdgeLabel("|body|"))],
                                                                    flatten([ArrayOfVarDecl(argsNode.id, fromExp.args),
                                                                            ArrayOfCExp(bodyNode.id, fromExp.body)])))
                        (makeNodeDecl(gen("Params"), `[:]`),
                         makeNodeDecl(gen("Body"), "[:]")) :
    isLetExp(fromExp) || isLetrecExp(fromExp) ? ((bindingsNode: Node, bodyNode: Node)=> union([makeEdge(single || makeNodeRef(fromId), bindingsNode, makeEdgeLabel("|bindings|")),
                                                                                                makeEdge(makeNodeRef(fromId), bodyNode, makeEdgeLabel("|body|"))],
                                                                                            flatten([ArrayOfBinding(bindingsNode.id, fromExp.bindings),
                                                                                                    ArrayOfCExp(bodyNode.id, fromExp.body)])))
                        (makeNodeDecl(gen("Bindings"), `[:]`),
                         makeNodeDecl(gen("Body"), "[:]")) :
    isLitExp(fromExp) ? ((sexpvalNode: Node)=> isCompoundSExp(fromExp.val) ? union([makeEdge(single || makeNodeRef(fromId), sexpvalNode, makeEdgeLabel("|val|"))],
                                                                                CompoundSExpEdges(makeNodeRef(sexpvalNode.id).id, fromExp.val)) :
                                                [makeEdge(makeNodeRef(fromId), sexpvalNode, makeEdgeLabel("|val|"))])
                        (makeNodeDecl(gen(whichSexpValue(fromExp.val)), printNodeLabel(fromExp.val))) : 
    isSetExp(fromExp) ? ((varrefNode: Node, valcexpNode: Node)=> union([makeEdge(single || makeNodeRef(fromId), varrefNode, makeEdgeLabel("|var|")),
                                                                        makeEdge(makeNodeRef(fromId), valcexpNode, makeEdgeLabel("|val|"))],
                                                                        LastOne(valcexpNode.id, fromExp.val)))
                        (makeNodeDecl(gen(fromExp.var.tag), printNodeLabel(fromExp.var)),
                        makeNodeDecl(gen(fromExp.val.tag), printNodeLabel(fromExp.val))) : []

const ArrayOfCExp = (fromId: string, fromExp: CExp[]): Edge[] =>
    flatten(map((exp:CExp):Edge[]=> isAtomicExp(exp) ? [makeEdge(makeNodeRef(fromId), makeNodeDecl(gen(exp.tag), printNodeLabel(exp)))] :
                                                     ((cexpNode:Node)=> union([makeEdge(makeNodeRef(fromId), cexpNode)],
                                                                             LastOne(cexpNode.id, exp)))
                                                     (makeNodeDecl(gen(exp.tag), printNodeLabel(exp)))
                , fromExp)
            )

const ArrayOfVarDecl = (fromId: string, varDecl:VarDecl[]): Edge[] =>
    flatten(map((x:VarDecl) => singleVarDecl(fromId, x), varDecl))

const singleVarDecl= (fromId: string, varDecl: VarDecl): Edge[] =>
    ((vardeclNode:Node):Edge[]=> [makeEdge(makeNodeRef(fromId), vardeclNode)])
        (makeNodeDecl(gen("VarDecl"), printNodeLabel(varDecl)))

const ArrayOfBinding = (fromId: string, fromBinding: Binding[]): Edge[] => 
    flatten(map((x:Binding):Edge[] => ((bindingNode:Node)=> union([makeEdge(makeNodeRef(fromId), bindingNode)], 
                                                                singleBinding(bindingNode.id, x)))
                                        (makeNodeDecl(gen("Binding"), printNodeLabel(x))), 
            fromBinding))

const singleBinding = (fromId: string, fromBinding: Binding): Edge[] =>
    ((cexpNode: Node):Edge[]=>union([makeEdge(makeNodeRef(fromId), makeNodeDecl(gen("VarDecl"), printNodeLabel(fromBinding.var)), makeEdgeLabel(`|var|`)),
                                     makeEdge(makeNodeRef(fromId), cexpNode, makeEdgeLabel(`|val|`))],
                                    LastOne(cexpNode.id, fromBinding.val)))
    (makeNodeDecl(gen(fromBinding.val.tag), printNodeLabel(fromBinding.val)))

const CompoundSExpEdges = (fromId: string, fromCompoundSExp: CompoundSExp): Edge[] =>
    isCompoundSExp(fromCompoundSExp.val2) && !isCompoundSExp(fromCompoundSExp.val1) ?
                                            ((newCompoundNode: Node, sexpvalNode:Node )=> union([makeEdge(makeNodeRef(fromId), sexpvalNode, makeEdgeLabel("|val1|")),
                                                                                                makeEdge(makeNodeRef(fromId), newCompoundNode, makeEdgeLabel("|val2|"))],
                                                                                            CompoundSExpEdges((makeNodeRef(newCompoundNode.id)).id, fromCompoundSExp.val2)))
                                            (makeNodeDecl(gen(whichSexpValue(fromCompoundSExp.val2)), printNodeLabel(fromCompoundSExp.val2)),
                                            makeNodeDecl(gen(whichSexpValue(fromCompoundSExp.val1)), printNodeLabel(fromCompoundSExp.val1))) :
    isCompoundSExp(fromCompoundSExp.val1) && !isCompoundSExp(fromCompoundSExp.val2) ?
                                            ((newCompoundNode: Node, sexpvalNode:Node )=> union([makeEdge(makeNodeRef(fromId), sexpvalNode, makeEdgeLabel("|val2|")),
                                                                                                makeEdge(makeNodeRef(fromId), newCompoundNode, makeEdgeLabel("|val1|"))],
                                                                                            CompoundSExpEdges((makeNodeRef(newCompoundNode.id)).id, fromCompoundSExp.val1)))
                                            (makeNodeDecl(gen(whichSexpValue(fromCompoundSExp.val1)), printNodeLabel(fromCompoundSExp.val1)),
                                            makeNodeDecl(gen(whichSexpValue(fromCompoundSExp.val2)), printNodeLabel(fromCompoundSExp.val2))) :
    isCompoundSExp(fromCompoundSExp.val1) && isCompoundSExp(fromCompoundSExp.val2) ?
                                            ((newCompoundNode: Node, newCompoundNode2:Node )=> union([makeEdge(makeNodeRef(fromId), newCompoundNode2, makeEdgeLabel("|val1|")),
                                                                                                makeEdge(makeNodeRef(fromId), newCompoundNode, makeEdgeLabel("|val2|"))],
                                                                                            union(CompoundSExpEdges((makeNodeRef(newCompoundNode.id)).id, fromCompoundSExp.val1),
                                                                                                  CompoundSExpEdges((makeNodeRef(newCompoundNode.id)).id, fromCompoundSExp.val2))))
                                            (makeNodeDecl(gen(whichSexpValue(fromCompoundSExp.val1)), printNodeLabel(fromCompoundSExp.val1)),
                                            makeNodeDecl(gen(whichSexpValue(fromCompoundSExp.val2)), printNodeLabel(fromCompoundSExp.val2))) :
        [makeEdge(makeNodeRef(fromId), makeNodeDecl(gen(whichSexpValue(fromCompoundSExp.val1)), printNodeLabel(fromCompoundSExp.val1)), makeEdgeLabel("|val1|")),
        makeEdge(makeNodeRef(fromId), makeNodeDecl(gen(whichSexpValue(fromCompoundSExp.val2)), printNodeLabel(fromCompoundSExp.val2)), makeEdgeLabel("|val2|"))]

const whichSexpValue = (sexp: SExpValue): string=>
    isCompoundSExp(sexp) || isPrimOp(sexp) || isSymbolSExp(sexp) || isEmptySExp(sexp) ? sexp.tag :
    isNumber(sexp) ? "number" : isBoolean(sexp) ? "boolean" : isString(sexp) ? "string" : "" 
const printNodeLabel = <T>(exp: SExpValue | CExp | Exp | VarDecl | Program | T[] | Binding): string =>
    isProgram(exp) ? `[Program]` :
    isArray(exp) ? `[:]` :
    isEmptySExp(exp) ? `["EmptySExp"]` :
    isNumber(exp) ? `["number(${exp})"]` :
    isString(exp) ? `["string(${exp})"]` :
    isBoolean(exp) ? `["boolean(${exp})"]` :
    isPrimOp(exp) ? `["PrimOp(${exp.op})"]` :
    isSymbolSExp(exp) ? `["SymbolSExp(${exp.val})"]` :
    isCompoundSExp(exp) ? `["CompoundSexp"]` :
    isNumExp(exp) ? `["NumExp(${exp.val})"]` :
    isBoolExp(exp) ? `["BoolExp(${exp.val})"]` :
    isStrExp(exp) ? `["StrExp(${exp.val})"]` :
    isVarRef(exp) ? `["VarRef(${exp.var})"]` :
    isCompoundExp(exp) ? `[${exp.tag}]` :
    isDefineExp(exp) ? `[${exp.tag}]` : 
    isVarDecl(exp) ? `["VarDecl(${exp.var})"]` : 
    isBinding(exp) ? `[Binding]`: ""

export const makeGen = (): (v: string) => string => {
    let count: number = 0;
    return (v: string) => {
        count++;
        return `${v}__${count}`;
    };
};

const gen = (x:string): string =>
    x==="Program" ? progGen(x) :
    x==="Exps" ? expsGen(x) :
    x==="DefineExp" ? defineExpGen(x) :
    x==="NumExp" ? numExpGen(x) :
    x==="BoolExp" ? boolExpGen(x) :
    x==="StrExp" ? strExpGen(x) :
    x==="PrimOp" ? primOpGen(x) :
    x==="VarRef" ? varRefGen(x) :
    x==="VarDecl" ? varDeclGen(x) :
    x==="AppExp" ? appExpGen(x) :
    x==="IfExp" ? ifExpGen(x) :
    x==="ProcExp" ? procExpGen(x) :
    x==="LetExp" ? letExpGen(x) :
    x==="LitExp" ? litExpGen(x) :
    x==="LetrecExp" ? letrecExpGen(x) :
    x==="SetExp" ? setExpGen(x) :
    x==="Rands" ? randsGen(x) :
    x==="Params" ? paramsGen(x) :
    x==="Body" ? bodyGen(x) :
    x==="Binding" ? bindingGen(x) :
    x==="Bindings" ? bindingsGen(x) :
    x==="CompoundSExp" ? compoundSExpGen(x) :
    x==="CompoundSexp" ? compoundSExpGen(x) :
    x==="EmptySExp" ? emptySExpGen(x) :
    x==="EmptySexp" ? emptySExpGen(x) :
    x==="number" ? numGen(x) :
    x==="boolean" ? boolGen(x) :
    x==="string" ? strGen(x) : 
    failGen("")
    

const progGen= makeGen();
const expsGen = makeGen();
const defineExpGen = makeGen();
const numExpGen= makeGen();
const boolExpGen = makeGen();
const strExpGen = makeGen();
const primOpGen = makeGen();
const varRefGen = makeGen();
const varDeclGen = makeGen();
const appExpGen = makeGen();
const ifExpGen = makeGen();
const procExpGen = makeGen();
const letExpGen = makeGen();
const litExpGen = makeGen();
const letrecExpGen = makeGen();
const setExpGen = makeGen();
const randsGen = makeGen();
const paramsGen = makeGen();
const bodyGen = makeGen();
const bindingGen = makeGen();
const bindingsGen = makeGen();
const compoundSExpGen = makeGen();
const emptySExpGen = makeGen();
const numGen = makeGen();
const boolGen = makeGen();
const strGen = makeGen();
const failGen = makeGen();




///////////////////////////////////////////////////////////////////////////// 2.3

export const unparseMermaid = (exp: Graph): Result<string>=>
    makeOk(unparseHeader(exp.header) + (isCompoundGraph(exp.graphContent) ? unparseEdges(exp.graphContent.edges) : unparseNode(exp.graphContent.node)))

const unparseHeader = (header: Header): string =>
    header.header

const unparseNode = (node: NodeDecl): string =>
    node.id+node.label

const unparseEdges = (edges: Edge[]): string =>
    join(`\n\t`, map(unparseEdge, edges))

const unparseEdge = (edge: Edge): string =>
    `${isNodeDecl(edge.from) && isNodeDecl(edge.to)? edge.from.id+edge.from.label+` -->`+printEdgeLabel(edge)+" "+edge.to.id+edge.to.label :
        isNodeDecl(edge.from) && isNodeRef(edge.to)? edge.from.id+edge.from.label+` -->`+printEdgeLabel(edge)+" "+edge.to.id :
        isNodeRef(edge.from) && isNodeRef(edge.to)? edge.from.id+` -->`+printEdgeLabel(edge)+" "+edge.to.id :
        isNodeRef(edge.from) && isNodeDecl(edge.to) ? edge.from.id+` -->`+printEdgeLabel(edge)+" "+ edge.to.id+edge.to.label : ""}`

const printEdgeLabel = (edge: Edge): string =>
    (edge.edgeLabel===undefined) ? "": edge.edgeLabel.label


///////////////////////////////////////////////////////////////////////////// 2.3


export const L4toMermaid = (concrete: string): Result<string> =>
    concrete.startsWith("(L4", 0) ? 
    bind(bind(parseL4(concrete), mapL4toMermaid), unparseMermaid) :
    bind(bind(bind(parse(concrete), parseL4Exp), mapL4toMermaid), unparseMermaid)


/////////////////////////////////////////////////////////////////////////////

// let testAss1 = L4toMermaid(`(lambda (x y)((lambda (x) (+ x y)) (+ x x))1)`);
// isOk(testAss1) ? console.log(testAss1.value) : "";
// let testAss2 = L4toMermaid(`(define my-list '(1 2))`);
// isOk(testAss2) ? console.log(testAss2.value) : "";
// let test00 = L4toMermaid(`(if (< 3 5) #t #f)`);
// isOk(test00) ? console.log(test00.value) : "";
// let test0 = L4toMermaid(`(L4 1 #t "hello")`);
// isOk(test0) ? console.log(test0.value) : "";
// let test1 = L4toMermaid("(L4(define a (+ (+ 3 4) (+ 5 6))))");
// isOk(test1) ? console.log(test1.value): ""
// let test2 = L4toMermaid("(L4(define sum(lambda (h j) (+ h j)))(sum 1 2)(define a (sum (sum 3 4) (sum 5 6))))");
// isOk(test2) ? console.log(test2.value): ""
// let test3 = L4toMermaid("(L4(define a (+ (+ 3 4) (+ 5 6))))");
// isOk(test3) ? console.log(test3.value): ""
// let test4 = L4toMermaid("(L4(let (x 3) (3)))");
// isOk(test4) ? console.log(test4.value): ""
// let test5 = L4toMermaid("(L4 (lambda (x y) ((lambda (x) (+ x y)) (+ x x)) 1))");
// isOk(test5) ? console.log(test5.value): ""
// let test6 = L4toMermaid("(L4(define my-list '(1 2)))");
// isOk(test6) ? console.log(test6.value): ""
// let test7 = L4toMermaid("(L4 (define sum (lambda (h j) (+ h j)))(sum 1 2))");
// isOk(test7) ? console.log(test7.value): ""
// let test8 = L4toMermaid("(L4(define sum(lambda (h j) (+ h j)))(sum 1 2)(if (> (sum 4 5) 7) #t (- 7 9)))");
// isOk(test8) ? console.log(test8.value): ""
// let test9 = L4toMermaid("(L4(let ((x 1))(let ((y (+ x 1)))(+ (* y y) x))))");
// isOk(test9) ? console.log(test9.value): ""
// let test10 = L4toMermaid("(L4(let ((x 1))(+ (* x x) x)))");
// isOk(test10) ? console.log(test10.value): ""
// let test11 = L4toMermaid("(L4(define make-adder(lambda (c)(lambda (x) (+ x c))))(let ((a3 (make-adder 3)))(let ((c 1))(a3 2))))");
// isOk(test11) ? console.log(test11.value): ""
// let test12 = L4toMermaid(`(L4 (let ((x 1)(y 2)(z 3))))`);
// isOk(test12) ? console.log(test12.value) : "";
// let test13 = L4toMermaid(`(L4 (lambda (x y)(lambda (z)(lambda (w t s)(#t)))))`);
// isOk(test13) ? console.log(test13.value) : "";
// let test14 = bind(mapL4toMermaid(makeProcExp([makeVarDecl("x")], [makeAppExp(makePrimOp("*"), [makeNumExp(1)])])), unparseMermaid)
// isOk(test14) ? console.log(test14.value) : "";
let test15 = L4toMermaid("(L4(define z (lambda (x) (* x x)))(((lambda (x) (lambda (z) (x z))) (lambda (w) (z w))) 2))");
isOk(test15) ? console.log(test15.value) : "";