import { map, fromPairs } from "ramda";
import { Sexp, Token } from "s-expression";
import { allT, first, second, rest, isEmpty } from "../shared/list";
import { isArray, isString, isNumericString, isIdentifier } from "../shared/type-predicates";
import { parse as p, isSexpString, isToken } from "../shared/parser";
import { Result, makeOk, makeFailure, bind, mapResult, safe2 } from "../shared/result";

export type Dir = "TD" | "LR";
export type GraphContent = AtomicGraph | CompoundGraph;
export type Node = NodeDecl | NodeRef;

export interface Graph {tag: "Graph"; header: Header; graphContent: GraphContent; } // TODO
export interface CompoundGraph {tag: "CompoundGraph"; edges: Edge[]; }
export interface AtomicGraph {tag: "AtomicGraph"; node: NodeDecl; }
export interface Header {tag: "Header"; type: Dir; header: string } // TODO - should it be string or GraphType?
export interface NodeDecl {tag: "NodeDecl"; id: string; label: string; }
export interface NodeRef {tag: "NodeRef"; id: string; }
export interface Edge {tag: "Edge"; from: Node; to: Node; edgeLabel?:EdgeLabel; }
export interface EdgeLabel {tag: "EdgeLabel"; label: string; }

// Type value constructors for disjoint types
export const makeGraph = (dir: Dir, graphContent: GraphContent): Graph => 
                            ({tag: "Graph", header: makeHeader(dir), graphContent: graphContent});
export const makeCompoundGraph = (edges: Edge[]): CompoundGraph => ({tag: "CompoundGraph", edges: edges});
export const makeAtomicGraph = (node: NodeDecl): AtomicGraph => ({tag: "AtomicGraph", node: node});
export const makeHeader = (type: Dir): Header => ({tag: "Header", type: type, header: `graph ${type}\n\t`}); // TODO
export const makeNodeDecl = (id: string, label: string): NodeDecl => ({tag: "NodeDecl", id: id, label: label});
export const makeNodeRef = (id: string): NodeRef => ({tag: "NodeRef", id: id});
export const makeEdge = (from: Node, to: Node, edgeLabel?: EdgeLabel): Edge => ({tag: "Edge", from: from, to: to, edgeLabel:edgeLabel});
export const makeEdgeLabel = (edgeLabel: string): EdgeLabel => ({tag: "EdgeLabel", label: edgeLabel});


// Type predicates for disjoint types
export const isGraph = (x: any): x is Graph => x.tag === "Graph";
export const isCompoundGraph = (x: any): x is CompoundGraph => x.tag === "CompoundGraph";
export const isAtomicGraph = (x: any): x is AtomicGraph => x.tag === "AtomicGraph";
export const isHeader = (x: any): x is Header => x.tag === "Header";
export const isNodeDecl = (x: any): x is NodeDecl => x.tag === "NodeDecl";
export const isNodeRef = (x: any): x is NodeRef => x.tag === "NodeRef";
export const isEdge = (x: any): x is Edge => x.tag === "Edge";
export const isEdgeLabel = (x: any): x is EdgeLabel => x.tag === "EdgeLabel";

// Type predicates for type unions
export const isGraphContent = (x: any): x is GraphContent => isAtomicGraph(x) || isCompoundGraph(x);
export const isNode = (x: any): x is Node => isNodeDecl(x) || isNodeRef(x);