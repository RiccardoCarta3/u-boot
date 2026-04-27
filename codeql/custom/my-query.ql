/**
 * @kind path-problem
 */

import cpp
import semmle.code.cpp.dataflow.TaintTracking

class NetworkByteSwap extends Expr {
  NetworkByteSwap () {
    exists(MacroInvocation m |
      m.getMacro().getName().matches("ntoh%") and
      this = m.getExpr()
    )
  }
}

module MyConfig implements DataFlow::ConfigSig {

  predicate isSource(DataFlow::Node source) {
    // Il nodo sorgente deve essere un'espressione della nostra classe
    source.asExpr() instanceof NetworkByteSwap
  }

  predicate isSink(DataFlow::Node sink) {
    // Il nodo di destinazione deve essere il 3° argomento (indice 2) di una memcpy
    exists(FunctionCall fc |
      fc.getTarget().hasName("memcpy") and
      sink.asExpr() = fc.getArgument(2)
    )
  }

import semmle.code.cpp.dataflow.DataFlow

   predicate isBarrier(DataFlow::Node node) {
    exists(DataFlow::Node n, RelationalOperation ro |
      DataFlow::localFlow(node, n) and
      n.asExpr() = ro.getAnOperand()
    )
  }
}

module MyTaint = TaintTracking::Global<MyConfig>;
import MyTaint::PathGraph

from MyTaint::PathNode source, MyTaint::PathNode sink
where MyTaint::flowPath(source, sink) 
select sink, source, sink, "Tint Propagation Trovato"
