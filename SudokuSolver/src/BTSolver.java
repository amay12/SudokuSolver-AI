import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

public class BTSolver
{

	// =================================================================
	// Properties
	// =================================================================

	private ConstraintNetwork network;
	private SudokuBoard sudokuGrid;
	private Trail trail;

	private boolean hasSolution = false;

	public String varHeuristics;
	public String valHeuristics;
	public String cChecks;

	// =================================================================
	// Constructors
	// =================================================================

	public BTSolver ( SudokuBoard sboard, Trail trail, String val_sh, String var_sh, String cc )
	{
		this.network    = new ConstraintNetwork( sboard );
		this.sudokuGrid = sboard;
		this.trail      = trail;

		varHeuristics = var_sh;
		valHeuristics = val_sh;
		cChecks       = cc;
	}

	// =================================================================
	// Consistency Checks
	// =================================================================

	// Basic consistency check, no propagation done
	private boolean assignmentsCheck ( )
	{
		for ( Constraint c : network.getConstraints() )
			if ( ! c.isConsistent() )
				return false;

		return true;
	}

	// =================================================================
	// Arc Consistency
	// =================================================================
	public boolean arcConsistency ( )
    {
        List<Variable> toAssign = new ArrayList<Variable>();
        List<Constraint> RMC = network.getModifiedConstraints();
        for(int i = 0; i < RMC.size(); ++i)
        {
            List<Variable> LV = RMC.get(i).vars;
            for(int j = 0; j < LV.size(); ++j)
            {
                if(LV.get(j).isAssigned())
                {
                    List<Variable> Neighbors = network.getNeighborsOfVariable(LV.get(j));
                    int assignedValue = LV.get(j).getAssignment();
                    for(int k = 0; k < Neighbors.size(); ++k)
                    {
                        Domain D = Neighbors.get(k).getDomain();
                        if(D.contains(assignedValue))
                        {
                            if(D.size() == 1)
                                return false;
                            if(D.size() == 2)
                                toAssign.add(Neighbors.get(k));
                            trail.push(Neighbors.get(k));
                            Neighbors.get(k).removeValueFromDomain(assignedValue);
                        }
                    }
                }
            }
        }
        if(!toAssign.isEmpty())
        {
            for(int i = 0; i < toAssign.size(); ++i)
            {
                Domain D = toAssign.get(i).getDomain();
                ArrayList<Integer> assign = D.getValues();
                trail.push(toAssign.get(i));
                toAssign.get(i).assignValue(assign.get(0));
            }
            return arcConsistency();
        }
        return network.isConsistent();
    }


	/**
	 * Part 1 TODO: Implement the Forward Checking Heuristic
	 *
	 * This function will do both Constraint Propagation and check
	 * the consistency of the network
	 *
	 * (1) If a variable is assigned then eliminate that value from
	 *     the square's neighbors.
	 *
	 * Note: remember to trail.push variables before you change their domain
	 *
	 * Return: a pair of a HashMap and a Boolean. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
	 *         The Boolean is true if assignment is consistent, false otherwise.
	 */
	
	public Map.Entry<HashMap<Variable,Domain>, Boolean> forwardChecking ( )
	{
		List<Constraint> modifiedConstraints = network.getModifiedConstraints();
		HashMap<Variable,Domain> fcMap = new HashMap<>();
		for(Constraint c: modifiedConstraints) {
			for(Variable var: c.vars) {
				if(var.isAssigned()) {
					Integer val = var.getAssignment();
					List<Variable> neighbours = network.getNeighborsOfVariable(var);
					for(Variable neighbour : neighbours) {
						if(neighbour.getDomain().contains(val)) {
							trail.push(neighbour);
							neighbour.removeValueFromDomain(val);
							if(neighbour.getDomain().size() == 0)
								return Pair.of(fcMap, false);
							fcMap.put(neighbour, neighbour.getDomain());
						}
					}
				}
			}
		}

		return Pair.of(fcMap, true);
	}
	
	/**
	 * Part 2 TODO: Implement both of Norvig's Heuristics
	 *
	 * This function will do both Constraint Propagation and check
	 * the consistency of the network
	 *
	 * (1) If a variable is assigned then eliminate that value from
	 *     the square's neighbors.
	 *
	 * (2) If a constraint has only one possible place for a value
	 *     then put the value there.
	 *
	 * Note: remember to trail.push variables before you change their domain
	 * Return: a pair of a map and a Boolean. The map contains the pointers to all variables that were assigned during the whole 
	 *         NorvigCheck propagation, and mapped to the values that they were assigned. 
	 *         The Boolean is true if assignment is consistent, false otherwise.
	 */
	public Map.Entry<HashMap<Variable,Integer>,Boolean> norvigCheck ( )
    {
	    
        //First check
        Map.Entry<HashMap<Variable,Domain>, Boolean> norvigFirst = forwardChecking();
        Boolean answer= norvigFirst.getValue();
        HashMap<Variable,Integer> variableValueMap = new HashMap<>();
        if(!answer) return Pair.of(variableValueMap, false);
        
        int N = sudokuGrid.getN();
        //second check
        List<Constraint> modifiedConstraints= network.getModifiedConstraints();

	    for(Constraint c: modifiedConstraints) {
	        for(Variable var: c.vars) {
	            if(!var.isAssigned()) {
	                int row = var.row();
	                int col = var.col();
	                int[] counter = new int[N + 1];
	
	                //Sorting neighbours into row, col, block neighbours
	                List<Variable> neighbours = network.getNeighborsOfVariable(var);
	                List<Variable> rowNeighbours = new ArrayList<>();
	                List<Variable> colNeighbours = new ArrayList<>();
	                List<Variable> blockNeighbours = new ArrayList<>();
	                rowNeighbours.add(var);
	                colNeighbours.add(var);
	                blockNeighbours.add(var);
	                for(Variable v: neighbours) {
	                    if(v.row() == row)
	                        rowNeighbours.add(v);
	                    if(v.col() == col)
	                        colNeighbours.add(v);
	                    if(v.block() == var.block())
	                        blockNeighbours.add(v);
	                }
	
	                //Iterating over row neighbours
	                for(Variable neighbour: rowNeighbours) {
	                    Domain domain = neighbour.getDomain();
	                    for(Integer val : domain.getValues()) {
	                        counter[val]++;
	                    }
	                }
	                //Boolean rowFlag = false;
	                for(int i = 1; i < counter.length; i++) {
	                    if(counter[i] == 1) {
	                        for(Variable neighbour: rowNeighbours) {
	                            if(!neighbour.isAssigned() && neighbour.getDomain().contains(i)) {
	                                trail.push(neighbour);
	                                neighbour.assignValue(i);
	                                variableValueMap.put(neighbour, i);
	                                norvigFirst = forwardChecking();
	                                answer = norvigFirst.getValue();
	                                //rowFlag = true;
	                                if(!answer) return Pair.of(variableValueMap, false);
	                                break;
	                            }
	                        }
	                    }
	                }
	                Arrays.fill(counter, 0);
	
	                //Iterating over column neighbours
	                for(Variable neighbour: colNeighbours) {
	                    Domain domain = neighbour.getDomain();
	                    for(Integer val : domain.getValues()) {
	                        counter[val]++;
	                    }
	                }
	                //Boolean colFlag = false;
	                for(int i = 1; i < counter.length; i++) {
	                    if(counter[i] == 1) {
	                        for(Variable neighbour: colNeighbours) {
	                            if(!neighbour.isAssigned() && neighbour.getDomain().contains(i)) {
	                                trail.push(neighbour);
	                                neighbour.assignValue(i);
	                                variableValueMap.put(neighbour, i);
	                                norvigFirst = forwardChecking();
	                                answer = norvigFirst.getValue();
	                                //colFlag = true;
	                                if(!answer) return Pair.of(variableValueMap, false);
	                                break;
	                            }
	                        }
	                    }
	                }
	                Arrays.fill(counter, 0);
	
	                //Iterating over block neighbours
	                for(Variable neighbour: blockNeighbours) {
	                    Domain domain = neighbour.getDomain();
	                    for(Integer val : domain.getValues()) {
	                        counter[val]++;
	                    }
	                }
	
	                for(int i = 1; i < counter.length; i++) {
	                    if(counter[i] == 1) {
	                        for(Variable neighbour: blockNeighbours) {
	                            if(!neighbour.isAssigned() && neighbour.getDomain().contains(i)) {
	                                trail.push(neighbour);
	                                neighbour.assignValue(i);
	                                variableValueMap.put(neighbour, i);
	                                norvigFirst = forwardChecking();
	                                answer = norvigFirst.getValue();
	                                if(!answer) return Pair.of(variableValueMap, false);
	                                break;
	                            }
	                        }
	                    }
	                }
	            }
	        }
        }

        return Pair.of(variableValueMap, true);
    }

	/**
	 * Optional TODO: Implement your own advanced Constraint Propagation
	 *
	 * Completing the three tourn heuristic will automatically enter
	 * your program into a tournament.
	 */
	private boolean getTournCC ( )
	{
		return norvigCheck().getValue();
	}

	// =================================================================
	// Variable Selectors
	// =================================================================

	// Basic variable selector, returns first unassigned variable
	private Variable getfirstUnassignedVariable()
	{
		for ( Variable v : network.getVariables() )
			if ( ! v.isAssigned() )
				return v;

		// Everything is assigned
		return null;
	}

	/**
	 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
	 *
	 * Return: The unassigned variable with the smallest domain
	 */
	public Variable getMRV ( )
	{
		//System.out.println("Yeah MR.V");
		List<Variable> allVars = network.getVariables();
		int smallestDomainSize = Integer.MAX_VALUE;
		Variable smallestDomainVar = null;
		// Loop for all variables to retrieve the minimum number of domains
		for(Variable v: allVars) {
			if(!v.isAssigned()) {
				int tempSize = v.getDomain().size();
				if(smallestDomainSize > tempSize) {
					smallestDomainSize = tempSize;
					smallestDomainVar = v;
				}
			}
			
		}
        return smallestDomainVar;
	}

	/**
	 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
	 *                with Degree Heuristic as a Tie Breaker
	 *
	 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
	 *         If there are multiple variables that have the same smallest domain with the same number 
	 *         of unassigned neighbors, add them to the list of Variables.
	 *         If there is only one variable, return the list of size 1 containing that variable.
	 */
	public List<Variable> MRVwithTieBreaker ( )
	{
	        List<Variable> qualifiedVariableList = new ArrayList<>();
	        List<Variable> finalVariableList = new ArrayList<>();
	        List<Variable> variables = network.getVariables();
	        int maxDegreeCount = -1, minSize = Integer.MAX_VALUE;
	        int domainSize = 0;

	        for(Variable var : variables) {
	            if(!var.isAssigned()) {
	                domainSize = var.getDomain().size();
	                minSize = Math.min(minSize, domainSize);
	            }
	        }

	        //Adding only the variables with least domain size
	        for(Variable var : variables) {
	            if(var.getDomain().size() == minSize)
	                qualifiedVariableList.add(var);
	        }

	        if(qualifiedVariableList.size() == 1) {
	            return qualifiedVariableList;
	        }

	        if(qualifiedVariableList.size()==0){
	            qualifiedVariableList.add(null);
	            return qualifiedVariableList;
	        }

	        //Degree heuristic tie breaker logic
	        for(Variable var : qualifiedVariableList) {
	            List<Variable> neighbours = network.getNeighborsOfVariable(var);
	            int degreeCount = 0;
	            for(Variable x: neighbours) {
	                if(!x.isAssigned()) {
	                    degreeCount++;
	                }
	            }
	            maxDegreeCount = Math.max(maxDegreeCount, degreeCount);
	        }

	        for(Variable var : qualifiedVariableList) {
	            List<Variable> neighbours = network.getNeighborsOfVariable(var);
	            int degreeCount = 0;
	            for(Variable x: neighbours) {
	                if(!x.isAssigned()) {
	                    degreeCount++;
	                }
	            }
	            if(degreeCount == maxDegreeCount) {
	                finalVariableList.add(var);
	            }
	        }

	        return finalVariableList;
        
		//return null;
    }

	/**
	 * Optional TODO: Implement your own advanced Variable Heuristic
	 *
	 * Completing the three tourn heuristic will automatically enter
	 * your program into a tournament.
	 */
	private Variable getTournVar ( )
	{
		return getMRV();
	}

	// =================================================================
	// Value Selectors
	// =================================================================

	// Default Value Ordering
	public List<Integer> getValuesInOrder ( Variable v )
	{
		List<Integer> values = v.getDomain().getValues();

		Comparator<Integer> valueComparator = new Comparator<Integer>(){

			@Override
			public int compare(Integer i1, Integer i2) {
				return i1.compareTo(i2);
			}
		};
		Collections.sort(values, valueComparator);
		return values;
	}

	/**
	 * Part 1 TODO: Implement the Least Constraining Value Heuristic
	 *
	 * The Least constraining value is the one that will knock the least
	 * values out of it's neighbors domain.
	 *
	 * Return: A list of v's domain sorted by the LCV heuristic
	 *         The LCV is first and the MCV is last
	 */
	public List<Integer> getValuesLCVOrder ( Variable v )
	{
		Domain d = v.getDomain();
		List<Variable> neighbors = network.getNeighborsOfVariable(v);
		List<Integer> result = new ArrayList<>();
		Map<Integer, List<Integer>> map = new TreeMap<>(); // Map of conflicts, List of dValues
		//Loop for each domain value
		for(int dValue: d.getValues()) {
			//count the number of conflicts
			int conflict = 0;
			for(Variable neighbor: neighbors) {
					List<Integer> neighbourValueList = neighbor.getDomain().getValues();
					if(neighbourValueList.contains(dValue)) {
						conflict++;
					}
			}
			List<Integer> temp = map.containsKey(conflict)?map.get(conflict): new ArrayList<>();
			temp.add(dValue);
			map.put(conflict,temp);
		}
		//Create a sorted list using the Map Values
		for(int key: map.keySet()) {
			List<Integer> temp = map.get(key);
			for(int value: temp) {
				result.add(value);
			}
		}
        return result;
	}

	/**
	 * Optional TODO: Implement your own advanced Value Heuristic
	 *
	 * Completing the three tourn heuristic will automatically enter
	 * your program into a tournament.
	 */
	public List<Integer> getTournVal ( Variable v )
	{
		return getValuesLCVOrder(v);
	}

	//==================================================================
	// Engine Functions
	//==================================================================

	public int solve (float time_left)
	{
		if(time_left <= 60.0) {
			return -1;
		}
		long startTime = System.nanoTime();
		if ( hasSolution )
			return 0;

		// Variable Selection
		Variable v = selectNextVariable();

		if ( v == null )
		{
			for ( Variable var : network.getVariables() )
			{
				// If all variables haven't been assigned
				if ( ! var.isAssigned() )
				{
					return 0;
				}
			}

			// Success
			hasSolution = true;
			return 0;
		}

		// Attempt to assign a value
		for ( Integer i : getNextValues( v ) )
		{
			// Store place in trail and push variable's state on trail
			trail.placeTrailMarker();
			trail.push( v );

			// Assign the value
			v.assignValue( i );

			// Propagate constraints, check consistency, recurse
			if ( checkConsistency() ) {
				long endTime = System.nanoTime();
                long elapsedTime = (endTime - startTime);
                float elapsedSecs = ((float)(endTime - startTime)) / 1000000000;
                float new_start_time = time_left - elapsedSecs;
				int check_status = solve(new_start_time);
				if(check_status == -1) {
				    return -1;
				}
			}

			// If this assignment succeeded, return
			if ( hasSolution )
				return 0;

			// Otherwise backtrack
			trail.undo();
		}
		return 0;
	}

	public boolean checkConsistency ( )
	{
		switch ( cChecks )
		{
			case "forwardChecking":
				return forwardChecking().getValue();

			case "norvigCheck":
				return norvigCheck().getValue();

			case "tournCC":
				return getTournCC();

			default:
				return assignmentsCheck();
		}
	}

	public Variable selectNextVariable ( )
	{
		switch ( varHeuristics )
		{
			case "MinimumRemainingValue":
				return getMRV();

			case "MRVwithTieBreaker":
				return MRVwithTieBreaker().get(0);

			case "tournVar":
				return getTournVar();

			default:
				return getfirstUnassignedVariable();
		}
	}

	public List<Integer> getNextValues ( Variable v )
	{
		switch ( valHeuristics )
		{
			case "LeastConstrainingValue":
				return getValuesLCVOrder( v );

			case "tournVal":
				return getTournVal( v );

			default:
				return getValuesInOrder( v );
		}
	}

	public boolean hasSolution ( )
	{
		return hasSolution;
	}

	public SudokuBoard getSolution ( )
	{
		return network.toSudokuBoard ( sudokuGrid.getP(), sudokuGrid.getQ() );
	}

	public ConstraintNetwork getNetwork ( )
	{
		return network;
	}
}
