/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package kodkod.engine.satlab;

import java.util.NoSuchElementException;
import kodkod.ast.Node;
import kodkod.engine.Solver;
import org.sat4j.core.VecInt;
import org.sat4j.maxsat.WeightedMaxSatDecorator;
import org.sat4j.pb.IPBSolver;
import org.sat4j.specs.ContradictionException; 
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;

/**
 *
 * @author praghletoos
 */
final public class WMaxSat4J implements SATSolver{
        private WeightedMaxSatDecorator solver; 
	private Boolean sat; 
	private int vars, clauses;
	
	/**
	 * Constructs a wrapper for the given instance
	 * of ISolver.
	 * @throws NullPointerException  solver = null
	 */
	WMaxSat4J(IPBSolver solver) {
		if (solver==null)
			throw new NullPointerException("solver");
		this.solver = new WeightedMaxSatDecorator(solver); 
		this.sat = null;
		this.vars = this.clauses = 0;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#numberOfVariables()
	 */
	public int numberOfVariables() {
		return vars; 
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#numberOfClauses()
	 */
	public int numberOfClauses() {
		return clauses; 
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#addVariables(int)
	 */
	public void addVariables(int numVars) {
		if (numVars < 0)
			throw new IllegalArgumentException("numVars < 0: " + numVars);
		else if (numVars > 0) {
			vars += numVars;
			solver.newVar(vars);
		}
	}
        private int[] shrinkIt(int[] lits){
            if(lits.length>1){
                int[] res = new int[lits.length-1];
                for(int i=0;i<res.length;i++){
                    res[i] = lits[i];
                }
                return res;
            }
            return null;
        }

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#addClause(int[])
	 */
	public boolean addClause(int[] lits) {
		try {
			if (!Boolean.FALSE.equals(sat)) {
				clauses++;
//                                for(int lit : lits) {
//					System.out.print(lit + " ");
//				}
//                                System.out.println(0);
                                if(lits[lits.length-1] == Node.default_priotiy){
                                    solver.addHardClause(new VecInt(shrinkIt(lits)));
                                }else{
                                    solver.addSoftClause(lits[lits.length-1],new VecInt(shrinkIt(lits)));
                                }
				
//				solver.addSoftClause( new VecInt(lits));
                                
				
				
				return true;
			}
			
		} catch (Exception e) {
			sat = Boolean.FALSE;
		}
		return false;
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#solve()
	 */
	public boolean solve() {
		try {
			if (!Boolean.FALSE.equals(sat))
				sat = Boolean.valueOf(solver.isSatisfiable());
			return sat;
		} catch (org.sat4j.specs.TimeoutException e) {
			throw new RuntimeException("timed out");
		} 
	}

	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#valueOf(int)
	 */
	public final boolean valueOf(int variable) {
		if (!Boolean.TRUE.equals(sat)) 
			throw new IllegalStateException();
		if (variable < 1 || variable > vars)
			throw new IllegalArgumentException(variable + " !in [1.." + vars+"]");
		return solver.model(variable);
	}
	
	/**
	 * {@inheritDoc}
	 * @see kodkod.engine.satlab.SATSolver#free()
	 */
	public synchronized final void free() {
		solver = null;
	}
	
	 

	

}
