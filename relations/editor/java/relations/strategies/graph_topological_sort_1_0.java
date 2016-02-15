package relations.strategies;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Stack;

import org.spoofax.interpreter.terms.IStrategoList;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.spoofax.interpreter.terms.ITermFactory;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

/**
 * Implements a topological sort of the strongly connected components in the graph using the Tarjan algorithm.
 * http://en.wikipedia.org/wiki/Tarjan's_strongly_connected_components_algorithm
 * http://dx.doi.org/10.1137/0201010
 *
 * <code>
 *  external graph-topological-sort(traverse-edges|)
 * </code>
 *
 * @see InteropRegisterer This class registers graph_topological_sort_1_0 for use.
 */
public class graph_topological_sort_1_0 extends Strategy {

	public static graph_topological_sort_1_0 instance = new graph_topological_sort_1_0();
	
	@Override
	public IStrategoTerm invoke(Context context, IStrategoTerm current, Strategy s1) {
		termToNode = new HashMap<IStrategoTerm, Node>();
		nodes = new ArrayList<Node>();
		
		if (current.getTermType() != IStrategoTerm.LIST) {
			context.getIOAgent().printError("graph-topological-sort: expected list as current term, actual value: " + current);
			context.popOnFailure();
			return null;
		}
		Iterator<IStrategoTerm> it = ((IStrategoList)current).iterator();
		while (it.hasNext()) {
			IStrategoTerm term = it.next();
			Node node = new Node(term);
			nodes.add(node);
			termToNode.put(term, node);
		}
		for(Node node : nodes){
			IStrategoTerm neighboursTerm = s1.invoke(context, node.term);
			if (neighboursTerm.getTermType() != IStrategoTerm.LIST) {
				context.getIOAgent().printError("graph-topological-sort: expected list as neighbours, actual value: " + neighboursTerm + " neighbours of: " + node.term);
				context.popOnFailure();
				return null;
			}
			Iterator<IStrategoTerm> it2 = ((IStrategoList)neighboursTerm).iterator();
			while (it2.hasNext()) {
				IStrategoTerm neighbourTerm = it2.next();
				if(!termToNode.containsKey(neighbourTerm)){
					context.getIOAgent().printError("graph-topological-sort: expected neighbour to be equal to one of the nodes, actual value: " + neighbourTerm);
				}else{
					Node neighbour = termToNode.get(neighbourTerm);
					node.neighbours.add(neighbour);
				}
			}
		}
		
		Collections.reverse(nodes);
		tarjan();
		Collections.reverse(sccs); // tarjan algorithm returns a reversed dependency graph
		
		ITermFactory factory = context.getFactory();
		List<IStrategoTerm> sccsTerms = new ArrayList<IStrategoTerm>();
		for(List<Node> scc : sccs){
			List<IStrategoTerm> sccTerms = new ArrayList<IStrategoTerm>();
			for(Node n : scc){
				sccTerms.add(n.term);
			}
			sccsTerms.add(factory.makeList(sccTerms));
		}
		return factory.makeList(sccsTerms);
	}
	
	final int UNDEFINED = -1;
	
	int index;
	Stack<Node> s;
	List<List<Node>> sccs;
	
	private void tarjan(){
		index = 0;
		s = new Stack<Node>();
		sccs = new ArrayList<List<Node>>();
		for(Node v : nodes){
			if(v.index == UNDEFINED){
				strongconnect(v);
			}
		}
	}
	
	private void strongconnect(Node v){
		v.index = index;
		v.lowlink = index;
		index++;
		s.push(v);
		v.onstack = true;
		for(Node w : v.neighbours){
			if(w.index == UNDEFINED){
				strongconnect(w);
				v.lowlink = Math.min(v.lowlink, w.lowlink);
			}
			else if(w.onstack){
				v.lowlink = Math.min(v.lowlink, w.index);
			}
		}
		if(v.lowlink == v.index){
			List<Node> scc = new ArrayList<Node>();
			Node w = null;
			do{
				w = s.pop();
				w.onstack = false;
				scc.add(w);
			}
			while(w != v);
			sccs.add(scc);
		}
	}
	
	HashMap<IStrategoTerm,Node> termToNode;
	List<Node> nodes;
	
	class Node{
		IStrategoTerm term;
		List<Node> neighbours;
		int index = UNDEFINED;
		int lowlink = UNDEFINED;
		boolean onstack = false;
		
		public Node(IStrategoTerm term){
			this.term = term;
			this.neighbours = new ArrayList<Node>();
		}
	}

}
